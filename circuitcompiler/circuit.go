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
	Inputs          []*Constraint
	Name            string
	rootConstraints map[Token]*Constraint
	//after reducing
	//constraintMap map[string]*Constraint
	constraintMap map[Token]*Constraint
}

func newCircuit(name string) *Circuit {
	return &Circuit{Name: name, constraintMap: make(map[Token]*Constraint), rootConstraints: make(map[Token]*Constraint)}
}

func (c *Circuit) isArgument(in Token) (isArg bool) {
	for _, v := range c.Inputs {
		if v.Output == in {
			return true
		}
	}
	return false
}

//recursively walks through the parse tree to create a list of all
//multiplication gates needed for the QAP construction
//Takes into account, that multiplication with constants and addition (= substraction) can be reduced, and does so
func (p *Program) build(currentCircuit *Circuit, currentConstraint *Constraint, hashTraceBuildup []byte, orderedmGates *[]*Gate, negate bool, invert bool) (facs factors, hashTraceResult []byte, variableEnd bool) {

	if currentConstraint.Output.Type == FUNCTION_CALL {
		nextCircuit := p.changeInputs(currentConstraint)
		currentCircuit = nextCircuit
		hashTraceBuildup = hashTogether(hashTraceBuildup, []byte(currentCircuit.currentOutputName()))
		for _, v := range nextCircuit.rootConstraints {
			p.build(nextCircuit, v, hashTraceBuildup, orderedmGates, negate, invert)
		}
		fac := &factor{typ: currentConstraint.Output, invert: invert, multiplicative: [2]int{1, 1}}
		return factors{fac}, hashTraceBuildup, true
	}

	if len(currentConstraint.Inputs) == 0 {
		if out, ex := p.computedInContext[string(hashTraceBuildup)][currentConstraint.Output]; ex {
			fac := &factor{typ: out.identifier, invert: invert, negate: negate, multiplicative: out.commonExtracted}
			return factors{fac}, hashTraceBuildup, true
		}
		switch currentConstraint.Output.Type {
		case NumberToken:
			b1, v1 := isValue(currentConstraint.Output.Value)
			if !b1 {
				panic("not a constant")
			}
			mul := [2]int{v1, 1}
			if invert {
				mul = [2]int{1, v1}
			}
			//return factors{{typ: CONST, negate: negate, multiplicative: mul}}, hashTraceBuildup, false
			return factors{{typ: currentConstraint.Output, negate: negate, multiplicative: mul}}, hashTraceBuildup, false
		case IdentToken:
			//TODO can this happen?
			//fac := &factor{typ: IN, name: currentConstraint.value.Out, invert: invert, negate: negate, multiplicative: [2]int{1, 1}}
			fac := &factor{typ: currentConstraint.Output, invert: invert, multiplicative: [2]int{1, 1}}
			return factors{fac}, hashTraceBuildup, true
		default:
			panic("")
		}
	}

	if len(currentConstraint.Inputs) == 1 {
		switch currentConstraint.Output.Type {
		case VAR:
			return p.build(currentCircuit, currentConstraint.Inputs[0], hashTraceBuildup, orderedmGates, negate, invert)
		default:
		}
	}

	if len(currentConstraint.Inputs) == 3 {
		//assert that the operation is in the middle..will cause truble i guess
		left := currentConstraint.Inputs[0]
		right := currentConstraint.Inputs[2]
		operation := currentConstraint.Inputs[1].Output

		leftFactors, hashLeft, variableAtLeftEnd := p.build(currentCircuit, left, hashTraceBuildup, orderedmGates, negate, invert)
		rightFactors, hashRight, variableAtRightEnd := p.build(currentCircuit, right, hashTraceBuildup, orderedmGates, Xor(negate, false), invert)

		switch operation.Type {
		case BinaryComperatorToken:
			break
		case BitOperatorToken:
			break
		case BooleanOperatorToken:
			break
		case ArithmeticOperatorToken:
			switch operation.Value {
			case "*":
				if !(variableAtLeftEnd && variableAtRightEnd) { //&& !currentConstraint.value.invert && currentConstraint != p.getMainCircuit().root {
					return mulFactors(leftFactors, rightFactors), hashTraceBuildup, variableAtLeftEnd || variableAtRightEnd
				}
				sig, newLef, newRigh := factorsSignature(leftFactors, rightFactors)
				if out, ex := p.computedFactors[sig.identifier]; ex {
					return factors{{typ: out.identifier, invert: invert, negate: negate, multiplicative: sig.commonExtracted}}, hashTraceBuildup, true
				}

				out := currentConstraint.Output.Value + string(hashTogether(hashLeft, hashRight)[:10])
				rootGate := &Gate{
					gateType: mgate,
					index:    len(*orderedmGates),
					value: &Constraint{
						Output: Token{
							Type:  0,
							Value: out,
						},
					},
					leftIns:  newLef,
					rightIns: newRigh,
				}

				p.computedInContext[string(hashTraceBuildup)][currentConstraint.Output] = MultiplicationGateSignature{identifier: currentConstraint.Output, commonExtracted: sig.commonExtracted}

				p.computedFactors[sig.identifier] = MultiplicationGateSignature{identifier: currentConstraint.Output, commonExtracted: sig.commonExtracted}
				*orderedmGates = append(*orderedmGates, rootGate)

				return factors{{typ: currentConstraint.Output, invert: invert, negate: negate, multiplicative: sig.commonExtracted}}, hashTraceBuildup, true

				return
			case "+":
				return addFactors(leftFactors, rightFactors), hashTraceBuildup, variableAtLeftEnd || variableAtRightEnd
				return
			}
			break
		case AssignmentOperatorToken:
			break
		default:
			panic("")
		}
	}
	panic("asdf")

}

func (circ *Circuit) updateRootsMap(constraint *Constraint) {
	for _, v := range constraint.Inputs {
		delete(circ.rootConstraints, v.Output)
	}
	circ.rootConstraints[constraint.Output] = constraint
}

func (circ *Circuit) SemanticCheck_RootMapUpdate(constraint *Constraint) {

	if ex := circ.isArgument(constraint.Output); ex {
		return
	}

	switch constraint.Output.Type {
	case NumberToken:
		return
	case FUNCTION_CALL:
		for _, in := range constraint.Inputs {
			//tmp := &Constraint{Out: in, Circuit: circ.Name}
			circ.SemanticCheck_RootMapUpdate(in)
		}
		circ.updateRootsMap(constraint)
		return
	case VAR:
		if _, ex := circ.constraintMap[constraint.Output]; ex {
			panic(fmt.Sprintf("variable %s already declared", constraint.Output.Value))
		}
		circ.constraintMap[constraint.Output] = constraint
		if len(constraint.Inputs) == 1 {
			circ.SemanticCheck_RootMapUpdate(constraint.Inputs[0])
			circ.updateRootsMap(constraint)
			return
		}
		if len(constraint.Inputs) == 3 {
			circ.SemanticCheck_RootMapUpdate(constraint.Inputs[0])
			circ.SemanticCheck_RootMapUpdate(constraint.Inputs[2])
			circ.updateRootsMap(constraint)
			return
		}
		panic("not supposed")

		return
	case RETURN:
		if len(constraint.Inputs) == 0 {
			return
		}
		if len(constraint.Inputs) == 1 {
			circ.SemanticCheck_RootMapUpdate(constraint.Inputs[0])
			circ.updateRootsMap(constraint)
			return
		}
		panic("not supposed")
		return
	default:
		panic("not implemented")

	}

}

func RegisterFunctionFromConstraint(constraint *Constraint) (c *Circuit) {

	name := constraint.Output.Value

	c = newCircuit(name)

	for _, arg := range constraint.Inputs {
		if ar, ex := c.constraintMap[arg.Output]; ex {
			panic(fmt.Sprintf("argument must be unique %v", ar))
		}
		//ng := &Gate{
		//	gateType: 0,
		//	index:    0,
		//	left:     nil,
		//	right:    nil,
		//	value:    arg,
		//	leftIns:  nil,
		//	rightIns: nil,
		//	expoIns:  nil,
		//}
		c.constraintMap[arg.Output] = arg

	}
	c.Inputs = constraint.Inputs
	return
}

//func (circ *Circuit) currentOutputName() string {
//
//	return composeNewFunction(circ.Name, circ.currentOutputs())
//}

//currentOutputs returns the composite name of the function/circuit with the recently assigned inputs
//func (circ *Circuit) currentOutputs() []string {
//
//	renamedInputs := make([]string, len(circ.Inputs))
//	for i, in := range circ.Inputs {
//		renamedInputs[i] = in.value.Out
//	}
//
//	return renamedInputs
//
//}

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
