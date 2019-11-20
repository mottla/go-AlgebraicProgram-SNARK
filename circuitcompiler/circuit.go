package circuitcompiler

import (
	"fmt"
	"regexp"
	"strconv"
	"strings"
)

var variableIndicationSign = "@"

// Circuit is the data structure of the compiled circuit
type Circuit struct {
	Inputs []*Gate
	Name   string
	roots   map[Token]*Gate
	//after reducing
	//constraintMap map[string]*Constraint
	gateMap map[Token]*Gate
}

func newCircuit(name string) *Circuit {
	return &Circuit{Name: name, gateMap: make(map[Token]*Gate)}
}

func (c *Circuit) isArgument(in Token) (isArg bool) {
	for _, v := range c.Inputs {
		if v.value.Output == in {
			return true
		}
	}
	return false
}

func (c *Circuit) buildTree(g *Gate) {


	if b, v := c.isArgument(g.value.Out); b {
		g.value = v
		return
	}

	if g.OperationType() == FUNC {
		for _, ingate := range g.value.Inputs {
			c.buildTree(ingate)
		}
		return
	}

	if gate, ex := c.gateMap[g.value.V1]; ex {
		g.left = gate
		c.buildTree(gate)
	}
	if gate, ex := c.gateMap[g.value.V2]; ex {
		g.right = gate
		c.buildTree(gate)
	}

}

func (circ *Circuit) UpdateRootsMap(token Token){
	if
}

func (circ *Circuit) SemanticCheck_AddGateMap(constraint *Constraint) {

	if ex := circ.isArgument(constraint.Output); ex {
		return
	}

	switch constraint.Output.Type {
	case NumberToken:
		return
	case FUNCTION_CALL:
		for _, in := range constraint.Inputs {
			//tmp := &Constraint{Out: in, Circuit: circ.Name}
			circ.SemanticCheck_AddGateMap(in)
		}
		circ.roots[constraint.Output] = &Gate{value: constraint}
		return
	case VAR:
		if _, ex := circ.gateMap[constraint.Output]; ex {
			panic(fmt.Sprintf("variable %s already declared", constraint.Output.Value))
		}
		gateToAdd := &Gate{value: constraint}
		circ.gateMap[constraint.Output] = gateToAdd
		if len(constraint.Inputs) == 1 {
			circ.SemanticCheck_AddGateMap(constraint.Inputs[0])
		}
		if len(constraint.Inputs) == 3 {
			circ.SemanticCheck_AddGateMap(constraint.Inputs[0])
			circ.SemanticCheck_AddGateMap(constraint.Inputs[2])
		}
		panic("not supposed")

		return
	case RETURN:
		circ.root = &Gate{value: constraint}
		if len(constraint.Inputs) == 0 {
			return
		}
		if len(constraint.Inputs) == 1 {
			circ.SemanticCheck_AddGateMap(constraint.Inputs[0])
		}
		panic("not supposed")
		return
	default:
		panic("not implemented")

	}

}

func registerFunctionFromConstraint(constraint *Constraint) (c *Circuit) {

	name := constraint.Output.Value

	c = newCircuit(name)

	constraintsToGates := make([]*Gate, len(constraint.Inputs))
	for i, arg := range constraint.Inputs {
		if ar, ex := c.gateMap[arg.Output]; ex {
			panic(fmt.Sprintf("argument must be unique %v", ar))
		}
		ng := &Gate{
			gateType: 0,
			index:    0,
			left:     nil,
			right:    nil,
			value:    arg,
			leftIns:  nil,
			rightIns: nil,
			expoIns:  nil,
		}
		c.gateMap[arg.Output] = ng
		constraintsToGates[i] = ng
	}
	c.Inputs = constraintsToGates
	return
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
