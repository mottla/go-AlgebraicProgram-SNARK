package circuitcompiler

import (
	"errors"
	"fmt"
	"regexp"
	"strconv"
	"strings"
)

var variableIndicationSign = "@"

type gateType uint8

const (
	mgate gateType = 1
	egate gateType = 2
)

// Circuit is the data structure of the compiled circuit
type Circuit struct {
	Inputs []*Gate
	Name   string
	root   *Gate
	//after reducing
	//constraintMap map[string]*Constraint
	gateMap map[string]*Gate
}

type Gate struct {
	gateType gateType
	index    int
	left     *Gate
	right    *Gate
	//funcInputs []*Gate
	value    *Constraint //is a pointer a good thing here??
	leftIns  factors     //leftIns and RightIns after addition gates have been reduced. only multiplication gates remain
	rightIns factors
	expoIns  factors
}

func (g Gate) String() string {
	return fmt.Sprintf("Gate %v : %v  with left %v right %v", g.index, g.value, g.leftIns, g.rightIns)
}

//type variable struct {
//	val string
//}

// Constraint is the data structure of a flat code operation
type Constraint struct {
	// v1 op v2 = out
	Circuit string //the name of the function, in which this constraint is defined. circuit/function names must be unique
	Op      Token
	V1      string
	V2      string
	Out     string
	//fV1  *variable
	//fV2  *variable
	//fOut *variable
	//Literal string
	//TODO once i've implemented a new parser/lexer we do this differently
	Inputs []*Gate // in func declaration case
	//fInputs []*variable
	negate bool
	invert bool
}

func (c Constraint) String() string {
	if c.negate || c.invert {
		return fmt.Sprintf("|%v = %v %v %v|  negated: %v, inverted %v", c.Out, c.V1, c.Op, c.V2, c.negate, c.invert)
	}
	return fmt.Sprintf("|%v = %v %v %v|", c.Out, c.V1, c.Op, c.V2)
}

func newCircuit(name string) *Circuit {
	return &Circuit{Name: name, gateMap: make(map[string]*Gate)}
}

func (p *Program) addFunction(constraint *Constraint) (c *Circuit) {

	b, name, args := isFunction(constraint.Out)
	if !b {
		panic(fmt.Sprintf("not a function: %v", constraint))
	}
	if _, ex := p.functions[name]; ex {
		panic("function already declared")
	}
	c = newCircuit(name)

	p.functions[name] = c

	renamedInputs := make([]*Gate, len(args))

	for i, in := range args {
		newConstr := &Constraint{
			Circuit: name,
			Op:      IN,
			Out:     in,
		}
		//c.prepareAndAddConstraintToGateMap(newConstr)
		renamedInputs[i] = &Gate{value: newConstr}
		c.gateMap[newConstr.Out] = renamedInputs[i]
	}
	c.Inputs = renamedInputs
	return
}

//prepareAndAddConstraintToGateMap takes a constraint as input, and renames its variables
//according to the circuit calling this function
//if the circuit is the main function circuit, then the constraint a = b * c becomes main@a = main@b * main@c
func (circ *Circuit) prepareAndAddConstraintToGateMap(constraint *Constraint) {
	if knownConstr, ex := circ.gateMap[constraint.Out]; ex {
		*constraint = *knownConstr.value
		return
	}
	if constraint.Out == "" {
		return
	}
	if arg, val := circ.isArgument(constraint.Out); arg {
		//lessons learned. if assigned without *, then the assignment is lost after the retrun
		*constraint = *val
		return

	}
	if constraint.Op == DIVIDE {
		constraint.Op = MULTIPLY
		constraint.invert = true
	}
	if constraint.Op == MINUS {
		constraint.Op = PLUS
		constraint.negate = true
	}

	if b, _ := isValue(constraint.Out); b {
		constraint.Op = CONST
		//return
	}

	if b, _, inputs := isFunction(constraint.Out); b {
		renamedInputs := make([]*Gate, len(inputs))
		for i, in := range inputs {
			tmp := &Constraint{Out: in, Circuit: circ.Name}
			circ.prepareAndAddConstraintToGateMap(tmp)
			renamedInputs[i] = &Gate{value: tmp}
		}
		//nn := composeNewFunction(name, renamedInputs)
		//constraint.Out = nn
		constraint.Inputs = renamedInputs
		constraint.Op = FUNC
		circ.gateMap[constraint.Out] = &Gate{value: constraint}
		return
	}
	gateToAdd := &Gate{value: constraint}
	left := &Constraint{Out: constraint.V1, Circuit: circ.Name}
	right := &Constraint{Out: constraint.V2, Circuit: circ.Name}
	circ.prepareAndAddConstraintToGateMap(left)
	circ.prepareAndAddConstraintToGateMap(right)
	constraint.V1 = left.Out
	constraint.V2 = right.Out
	//todo this is dangerous.. if someone would use out as variable name, things would be fucked
	if constraint.Out == "out" {
		constraint.Out = circ.Name //composeNewFunction(circ.Name, circ.Inputs)
		circ.root = gateToAdd
		circ.gateMap[constraint.Out] = gateToAdd
		return
	}

	//constraint.Out = circ.Name + variableIndicationSign + constraint.Out

	circ.gateMap[constraint.Out] = gateToAdd

}

func (circ *Circuit) currentOutputName() string {

	return composeNewFunction(circ.Name, circ.currentOutputs())
}

//currentOutputs returns the composite name of the function/circuit with the recently assigned inputs
func (circ *Circuit) currentOutputs() []string {

	renamedInputs := make([]string, len(circ.Inputs))
	for i, in := range circ.Inputs {
		renamedInputs[i] = in.value.Out
	}

	return renamedInputs

}

func composeNewFunction(fname string, inputs []string) string {
	builder := strings.Builder{}
	builder.WriteString(fname)
	builder.WriteRune('(')
	for i := 0; i < len(inputs); i++ {
		builder.WriteString(inputs[i])
		if i < len(inputs)-1 {
			builder.WriteRune(',')
		}
	}
	builder.WriteRune(')')
	return builder.String()
}

func max(a, b int) int {
	if a > b {
		return a
	}
	return b
}

func TreeDepth(g *Gate) int {
	return printDepth(g, 0)
}

func printDepth(g *Gate, d int) int {
	d = d + 1
	if g.left != nil && g.right != nil {
		return max(printDepth(g.left, d), printDepth(g.right, d))
	} else if g.left != nil {
		return printDepth(g.left, d)
	} else if g.right != nil {
		return printDepth(g.right, d)
	}
	return d
}
func CountMultiplicationGates(g *Gate) int {
	if g == nil {
		return 0
	}
	if len(g.rightIns) > 0 || len(g.leftIns) > 0 {
		return 1 + CountMultiplicationGates(g.left) + CountMultiplicationGates(g.right)
	} else {
		return CountMultiplicationGates(g.left) + CountMultiplicationGates(g.right)
	}
	return 0
}

func PrintTree(g *Gate) {
	printTree(g, 0)
}
func printTree(g *Gate, d int) {
	d += 1

	if g.leftIns == nil || g.rightIns == nil {
		fmt.Printf("Depth: %v - %s \t \t \t \t \n", d, g.value)
	} else {
		fmt.Printf("Depth: %v - %s \t \t \t \t with  l %v  and r %v\n", d, g.value, g.leftIns, g.rightIns)
	}

	if g.left != nil {
		printTree(g.left, d)
	}
	if g.right != nil {
		printTree(g.right, d)
	}
}

func Xor(a, b bool) bool {
	return (a && !b) || (!a && b)
}

func (g *Gate) ExtractValues(in []int) (er error) {
	if b, v1 := isValue(g.value.V1); b {
		if b2, v2 := isValue(g.value.V2); b2 {
			in = append(in, v1, v2)
			return nil
		}
	}
	return errors.New(fmt.Sprintf("Gate \"%s\" has no int values", g.value))
}

func (g *Gate) OperationType() Token {
	return g.value.Op
}

func isValue(a string) (bool, int) {
	v, err := strconv.Atoi(a)
	if err != nil {
		return false, 0
	}
	return true, v
}
func isFunction(a string) (tf bool, name string, inputs []string) {

	if !strings.ContainsRune(a, '(') && !strings.ContainsRune(a, ')') {
		return false, "", nil
	}
	name = strings.Split(a, "(")[0]

	// read string inside ( )
	rgx := regexp.MustCompile(`\((.*?)\)`)
	insideParenthesis := rgx.FindStringSubmatch(a)
	varsString := strings.Replace(insideParenthesis[1], " ", "", -1)
	inputs = strings.Split(varsString, ",")

	return true, name, inputs
}
