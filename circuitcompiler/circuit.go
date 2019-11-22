package circuitcompiler

import (
	"fmt"
	"strconv"
	"strings"
)

var variableIndicationSign = "@"

// Circuit is the data structure of the compiled circuit
type Circuit struct {
	Inputs            []*Constraint
	Name              string
	rootConstraints   map[string]*Constraint
	returnConstraints []*Constraint
	//after reducing
	//constraintMap map[string]*Constraint
	constraintMap map[string]*Constraint
}

func newCircuit(name string) *Circuit {
	return &Circuit{Name: name, constraintMap: make(map[string]*Constraint), rootConstraints: make(map[string]*Constraint)}
}

//only identtokens can be arguments
func (c *Circuit) isArgument(in Token) (isArg bool, arg *Constraint) {
	if in.Type == IdentToken {
		for _, v := range c.Inputs {
			if v.Output.Value == in.Value {
				return true, v
			}
		}
	}
	return false, nil
}

func (circ *Circuit) updateRootsMap(constraint *Constraint) {

	for _, v := range constraint.Inputs {
		delete(circ.rootConstraints, v.Output.Value)
	}
	circ.rootConstraints[constraint.Output.Value] = constraint
}

func (circ *Circuit) SemanticCheck_RootMapUpdate(constraint *Constraint) {

	if constraint.Output.Type&(ARGUMENT|NumberToken|binOp) != 0 {
		return
	}
	for i := 0; i < len(constraint.Inputs); i++ {
		//circ.SemanticCheck_RootMapUpdate(constraint.Inputs[i])

		if ex, arg := circ.isArgument(constraint.Inputs[i].Output); ex {
			constraint.Inputs[i] = arg
		}
		circ.SemanticCheck_RootMapUpdate(constraint.Inputs[i])
	}

	switch constraint.Output.Type {
	case IdentToken:
		if v, ex := circ.constraintMap[constraint.Output.Value]; ex {
			*constraint = *v
			break
		}
		panic(fmt.Sprintf("variable %s used but not declared", constraint.Output.Value))
	case IF:
		fmt.Println("dsaf")
		break
	case FUNCTION_CALL:
		break
	case EQUAL:

		break
	case VAR:
		if _, ex := circ.constraintMap[constraint.Output.Value]; ex {
			panic(fmt.Sprintf("variable %s already declared", constraint.Output.Value))
		}
		circ.constraintMap[constraint.Output.Value] = constraint
		break
	case RETURN:
		//constraint.Output.Value= fmt.Sprintf("%s%v",circ.Name,len(constraint.Output.Value))
		constraint.Output.Value = circ.Name
		circ.returnConstraints = append(circ.returnConstraints, constraint)
		break
	case UNASIGNEDVAR:
		circ.constraintMap[constraint.Output.Value] = constraint
		break
	default:
		panic(fmt.Sprintf("not implemented %v", constraint))

	}
	circ.updateRootsMap(constraint)
}

func RegisterFunctionFromConstraint(constraint *Constraint) (c *Circuit) {

	name := constraint.Output.Value
	c = newCircuit(name)

	duplicateMap := make(map[string]bool)
	for _, arg := range constraint.Inputs {

		if _, ex := duplicateMap[arg.Output.Value]; ex {
			panic("argument must be unique ")
		}
		duplicateMap[arg.Output.Value] = true
		////ng := &Gate{
		////	gateType: 0,
		////	index:    0,
		////	left:     nil,
		////	right:    nil,
		////	value:    arg,
		////	leftIns:  nil,
		////	rightIns: nil,
		////	expoIns:  nil,
		////}
		c.constraintMap[arg.Output.Value] = arg
	}
	c.Inputs = constraint.Inputs
	return
}

func (circ *Circuit) currentOutputName() string {

	return composeNewFunction(circ.Name, circ.currentOutputs())
}

//currentOutputs returns the composite name of the function/circuit with the recently assigned inputs
func (circ *Circuit) currentOutputs() []string {

	renamedInputs := make([]string, len(circ.Inputs))
	for i, in := range circ.Inputs {
		renamedInputs[i] = in.Output.Value
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
