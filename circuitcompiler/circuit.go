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
	//specialBuild  func(currentCircuit *Circuit, currentConstraint *Constraint, orderedmGates *[]*Gate, negate bool, invert bool, f func(currentCircuit *Circuit, currentConstraint *Constraint, orderedmGates *[]*Gate, negate, invert bool) (facs factors, variableEnd bool)) (facs factors, variableEnd bool)
}

func newCircuit(name string) *Circuit {
	c := &Circuit{Name: name, constraintMap: make(map[string]*Constraint), rootConstraints: make(map[string]*Constraint)}
	//c.specialBuild = func(currentCircuit *Circuit, currentConstraint *Constraint, orderedmGates *[]*Gate, negate bool, invert bool,i func(currentCircuit *Circuit, currentConstraint *Constraint, orderedmGates *[]*Gate, negate bool, invert bool) (facs factors, variableEnd bool)) (facs factors, variableEnd bool) {
	//	return i(currentCircuit, currentConstraint, orderedmGates, negate, invert)
	//}
	return c
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

	if constraint.Output.Type&(ARGUMENT|NumberToken|binOp|ARRAY_CALL) != 0 {
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
		//constraint.Output.Value = composeNewFunctionName(constraint)
		break
	case EQUAL:

		break
	case VAR:
		if _, ex := circ.constraintMap[constraint.Output.Value]; ex {
			panic(fmt.Sprintf("variable %s already declared", constraint.Output.Value))
		}
		circ.constraintMap[constraint.Output.Value] = constraint
		break
	case ARRAY_Define:

		for i := 0; i < len(constraint.Inputs); i++ {
			element := fmt.Sprintf("%s[%v]", constraint.Output.Value, i)
			circ.constraintMap[element] = constraint.Inputs[i]
		}
		return
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

func composeNewFunctionName(fkt *Constraint) string {
	builder := strings.Builder{}
	builder.WriteString(fkt.Output.Value)
	builder.WriteRune('(')
	for i := 0; i < len(fkt.Inputs); i++ {
		builder.WriteString(fkt.Inputs[i].Output.Value)
		if i < len(fkt.Inputs)-1 {
			builder.WriteRune(',')
		}
	}
	builder.WriteRune(')')
	return builder.String()
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
