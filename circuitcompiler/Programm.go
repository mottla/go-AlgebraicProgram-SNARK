package circuitcompiler

import (
	"fmt"
	"github.com/mottla/go-AlgebraicProgram-SNARK/circuitcompiler/fields"
	"math/big"
	"sort"
	"strings"
)

type MultiplicationGateSignature struct {
	identifier      Token
	commonExtracted [2]int //if the mgate had a extractable factor, it will be stored here
}

func (m MultiplicationGateSignature) String() string {
	return fmt.Sprintf("%s extracted %v", m.identifier.String(), m.commonExtracted)
}

type Program struct {
	functions    map[string]*Circuit
	globalInputs []Token
	Fields       fields.Fields //find a better name
	//to reduce the number of multiplication gates, we store each factor signature, and the variable name,
	//so each time a variable is computed, that happens to have the very same factors, we reuse the former
	//it boost setup and proof time
	computedFactors map[Token]MultiplicationGateSignature
}

func NewProgram(CurveOrder, FieldOrder *big.Int) (program *Program) {

	G := newCircuit("scalarBaseMultiply")
	E := newCircuit("equal")

	program = &Program{
		functions:    map[string]*Circuit{"scalarBaseMultiply": G, "equal": E},
		globalInputs: []Token{},
		Fields:       fields.PrepareFields(CurveOrder, FieldOrder),
	}

	return
}

//returns the cardinality of all main inputs + 1 for the "one" signal
func (p *Program) GlobalInputCount() int {
	return len(p.globalInputs)
}

func (p *Program) ReduceCombinedTree(functions map[string]*Circuit) (orderedmGates []*Gate) {

	for k, v := range functions {
		p.functions[k] = v
	}
	orderedmGates = []*Gate{}
	p.globalInputs = append(p.globalInputs, Token{
		Type:  NumberToken,
		Value: "1",
	})

	for _, rootC := range p.getMainCircuit().Inputs {
		p.globalInputs = append(p.globalInputs, rootC.Output)
	}

	p.computedFactors = make(map[Token]MultiplicationGateSignature)

	mainCircuit := p.getMainCircuit()

	for i := 0; i < mainCircuit.rootConstraints.len(); i++ {
		f, _ := p.build(p.getMainCircuit(), mainCircuit.rootConstraints.data[i], &orderedmGates, false, false)
		for _, fac := range f {
			for k := range orderedmGates {
				if orderedmGates[k].value.identifier.Value == fac.typ.Value {
					orderedmGates[k].output = p.Fields.ArithmeticField.FractionToField(invertVector(fac.multiplicative))
				}
			}
		}
	}
	return orderedmGates
}

func (p *Program) getMainCircuit() *Circuit {
	return p.functions["main"]
}

func (p *Program) changeInputs(constraint *Constraint) (nextContext *Circuit) {

	if constraint.Output.Type != FUNCTION_CALL {
		panic("not a function")
	}

	if newCircut, v := p.functions[strings.Split(constraint.Output.Value, "(")[0]]; v {

		if len(newCircut.Inputs) != len(constraint.Inputs) {
			panic("argument size missmatch")
		}

		for i, _ := range newCircut.Inputs {
			*newCircut.Inputs[i] = *constraint.Inputs[i]
		}
		//newCircut.returnConstraints[0].Output.Value = constraint.Output.Value

		return newCircut
	}
	panic("undeclared function call. check your source")
	return nil
}

//recursively walks through the parse tree to create a list of all
//multiplication gates needed for the QAP construction
//Takes into account, that multiplication with constants and addition (= substraction) can be reduced, and does so
func (p *Program) build(currentCircuit *Circuit, currentConstraint *Constraint, orderedmGates *[]*Gate, negate, invert bool) (facs factors, variableEnd bool) {

	if len(currentConstraint.Inputs) == 0 {
		switch currentConstraint.Output.Type {
		case NumberToken:
			b1, v1 := isValue(currentConstraint.Output.Value)
			if !b1 {
				panic("not a constant")
			}
			mul := [2]int{v1, 1}
			if invert {
				mul = invertVector(mul)
			}
			return factors{{typ: Token{Type: NumberToken}, negate: negate, multiplicative: mul}}, false
		case IdentToken:
			if con, ex := currentCircuit.constraintMap[currentConstraint.Output.Value]; ex {
				return p.build(currentCircuit, con, orderedmGates, negate, invert)
			}
			panic("asdf")
		case UNASIGNEDVAR:
			if con, ex := currentCircuit.constraintMap[currentConstraint.Output.Value]; ex {
				return p.build(currentCircuit, con, orderedmGates, negate, invert)
			}
			panic("asdf")
		case RETURN:
			panic("empty return not implemented yet")
			fac := factor{typ: Token{
				Type: NumberToken,
			}, negate: negate, multiplicative: [2]int{1, 1}}
			return factors{fac}, false
		case ARGUMENT:
			fac := factor{typ: Token{
				Type:  ARGUMENT,
				Value: currentConstraint.Output.Value, //+string(hashTraceBuildup),
			}, negate: negate, invert: invert, multiplicative: [2]int{1, 1}}
			return factors{fac}, true
		default:
			panic("")
		}
	}

	if currentConstraint.Output.Type == FUNCTION_CALL {
		switch currentConstraint.Output.Value {
		case "scalarBaseMultiply":
			currentConstraint.Output.Type = UNASIGNEDVAR
			secretFactors, _ := p.build(currentCircuit, currentConstraint, orderedmGates, false, false)
			currentConstraint.Output.Type = FUNCTION_CALL
			secretFactors.normalizeAll()
			sort.Sort(secretFactors)
			sig := hashToBig(secretFactors).String()[:16]

			nTok := Token{
				Type:  FUNCTION_CALL,
				Value: sig,
			}
			if _, ex := p.computedFactors[nTok]; !ex {
				rootGate := &Gate{
					gateType: egate,
					index:    len(*orderedmGates),
					value:    MultiplicationGateSignature{identifier: nTok, commonExtracted: [2]int{1, 1}},
					expoIns:  secretFactors,
					output:   big.NewInt(int64(1)),
				}
				p.computedFactors[nTok] = rootGate.value
				*orderedmGates = append(*orderedmGates, rootGate)
			}

			return factors{factor{
				typ:            nTok,
				invert:         invert,
				negate:         negate,
				multiplicative: [2]int{1, 1},
			}}, true
		case "equal":
			if len(currentConstraint.Inputs) < 2 {
				panic("equality constraint requires min 2 arguments")
			}
			//for _, arg := range currentConstraint.Inputs {
			//	//arg.
			//}
			secretFactors, _ := p.build(currentCircuit, currentConstraint, orderedmGates, false, false)
			currentConstraint.Output.Type = FUNCTION_CALL
			secretFactors.normalizeAll()
			sort.Sort(secretFactors)
			sig := hashToBig(secretFactors).String()[:16]

			nTok := Token{
				Type:  FUNCTION_CALL,
				Value: sig,
			}
			if _, ex := p.computedFactors[nTok]; !ex {
				rootGate := &Gate{
					gateType: egate,
					index:    len(*orderedmGates),
					value:    MultiplicationGateSignature{identifier: nTok, commonExtracted: [2]int{1, 1}},
					expoIns:  secretFactors,
					output:   big.NewInt(int64(1)),
				}
				p.computedFactors[nTok] = rootGate.value
				*orderedmGates = append(*orderedmGates, rootGate)
			}

			return factors{factor{
				typ:            nTok,
				invert:         invert,
				negate:         negate,
				multiplicative: [2]int{1, 1},
			}}, true
			return
		default:
			nextCircuit := p.changeInputs(currentConstraint)

			for i := 0; i < nextCircuit.rootConstraints.len()-1; i++ {
				p.build(nextCircuit, nextCircuit.rootConstraints.data[i], orderedmGates, false, false)
			}

			return p.build(nextCircuit, nextCircuit.rootConstraints.data[nextCircuit.rootConstraints.len()-1], orderedmGates, negate, invert)
		}

	}
	if currentConstraint.Output.Type == ARRAY_CALL {
		var tmpGates []*Gate
		nc := Constraint{Output: Token{Type: UNASIGNEDVAR}, Inputs: currentConstraint.Inputs}

		indexFactors, variable := p.build(currentCircuit, &nc, &tmpGates, false, false)
		if variable {
			panic("cannot access array dynamically in an arithmetic circuit currently")
		}
		if len(facs) > 1 {
			panic("unexpected")
		}
		elementName := fmt.Sprintf("%s[%v]", currentConstraint.Output.Value, int(indexFactors[0].multiplicative[0]/indexFactors[0].multiplicative[1]))
		if con, ex := currentCircuit.constraintMap[elementName]; ex {
			return p.build(currentCircuit, con, orderedmGates, negate, invert)
		}
		panic(fmt.Sprintf("entry %v not found", elementName))
	}

	if len(currentConstraint.Inputs) == 1 {
		switch currentConstraint.Output.Type {
		case VAR:
			return p.build(currentCircuit, currentConstraint.Inputs[0], orderedmGates, negate, invert)
		case RETURN:
			return p.build(currentCircuit, currentConstraint.Inputs[0], orderedmGates, negate, invert)
		case UNASIGNEDVAR:
			return p.build(currentCircuit, currentConstraint.Inputs[0], orderedmGates, negate, invert)
		case IdentToken:
			return p.build(currentCircuit, currentConstraint.Inputs[0], orderedmGates, negate, invert)
		default:
			panic("")
		}
	}

	if len(currentConstraint.Inputs) == 3 {

		left := currentConstraint.Inputs[2]
		right := currentConstraint.Inputs[1]
		operation := currentConstraint.Inputs[0].Output
		var leftFactors, rightFactors factors
		var variableAtLeftEnd, variableAtRightEnd bool

	out:
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
				leftFactors, variableAtLeftEnd = p.build(currentCircuit, left, orderedmGates, negate, false)
				rightFactors, variableAtRightEnd = p.build(currentCircuit, right, orderedmGates, negate, false)
				break out
			case "+":
				leftFactors, variableAtLeftEnd = p.build(currentCircuit, left, orderedmGates, Xor(negate, false), invert)
				rightFactors, variableAtRightEnd = p.build(currentCircuit, right, orderedmGates, Xor(negate, false), invert)
				return addFactors(leftFactors, rightFactors), variableAtLeftEnd || variableAtRightEnd
			case "/":
				leftFactors, variableAtLeftEnd = p.build(currentCircuit, left, orderedmGates, negate, false)
				rightFactors, variableAtRightEnd = p.build(currentCircuit, right, orderedmGates, negate, true)
				break out
			case "-":
				leftFactors, variableAtLeftEnd = p.build(currentCircuit, left, orderedmGates, Xor(negate, false), invert)
				rightFactors, variableAtRightEnd = p.build(currentCircuit, right, orderedmGates, Xor(negate, true), invert)
				return addFactors(leftFactors, rightFactors), variableAtLeftEnd || variableAtRightEnd
			}
			break
		case AssignmentOperatorToken:
			break
		default:
			panic("unsupported operation")
		}

		if !(variableAtLeftEnd && variableAtRightEnd) {
			return mulFactors(leftFactors, rightFactors), variableAtLeftEnd || variableAtRightEnd
		}
		sig, newLef, newRigh := factorsSignature(leftFactors, rightFactors)
		if out, ex := p.computedFactors[sig.identifier]; ex {
			return factors{{typ: out.identifier, invert: invert, negate: negate, multiplicative: sig.commonExtracted}}, true
		}
		//currentConstraint.Output.Value += "@"
		//currentConstraint.Output.Value += sig.identifier.Value
		nTok := Token{
			Type: currentConstraint.Output.Type,
			//Value: currentConstraint.Output.Value + "@" + sig.identifier.Value,
			Value: sig.identifier.Value,
		}
		rootGate := &Gate{
			gateType: mgate,
			index:    len(*orderedmGates),
			value:    MultiplicationGateSignature{identifier: nTok, commonExtracted: sig.commonExtracted},
			leftIns:  newLef,
			rightIns: newRigh,
			output:   big.NewInt(int64(1)),
		}

		p.computedFactors[sig.identifier] = MultiplicationGateSignature{identifier: nTok, commonExtracted: sig.commonExtracted}
		*orderedmGates = append(*orderedmGates, rootGate)

		return factors{{typ: nTok, invert: invert, negate: negate, multiplicative: sig.commonExtracted}}, true
	}

	panic(currentConstraint)
}

// GenerateR1CS generates the ER1CS polynomials from the Circuit
func (p *Program) GatesToR1CS(mGates []*Gate) (r1CS ER1CS) {
	// from flat code to ER1CS

	offset := len(p.globalInputs)
	//  one + in1 +in2+... + gate1 + gate2 .. + out
	size := offset + len(mGates)
	indexMap := make(map[Token]int)

	for i, v := range p.globalInputs {
		indexMap[v] = i
	}

	for _, v := range mGates {
		if _, ex := indexMap[v.value.identifier]; !ex {
			indexMap[v.value.identifier] = len(indexMap)
		} else {
			panic(fmt.Sprintf("rewriting %v ", v.value))
		}

	}

	insertValue := func(val factor, arr []*big.Int) {
		if val.typ.Type != NumberToken {
			if _, ex := indexMap[val.typ]; !ex {
				panic(fmt.Sprintf("%v index not found!!!", val))
			}
		}
		value := p.Fields.ArithmeticField.FractionToField(val.multiplicative)
		if val.negate {
			value = p.Fields.ArithmeticField.Neg(value)
		}
		//not that index is 0 if its a constant, since 0 is the map default if no entry was found
		arr[indexMap[val.typ]] = value
	}

	for _, g := range mGates {

		if g.gateType == mgate {
			aConstraint := fields.ArrayOfBigZeros(size)
			bConstraint := fields.ArrayOfBigZeros(size)
			eConstraint := fields.ArrayOfBigZeros(size)
			cConstraint := fields.ArrayOfBigZeros(size)

			for _, val := range g.leftIns {
				insertValue(val, aConstraint)
			}

			for _, val := range g.rightIns {
				insertValue(val, bConstraint)
			}
			cConstraint[indexMap[g.value.identifier]] = g.output

			//cConstraint[indexMap[g.value.identifier]] = big.NewInt(int64(1))

			if g.rightIns[0].invert {
				tmp := aConstraint
				aConstraint = cConstraint
				cConstraint = tmp
			}
			r1CS.L = append(r1CS.L, aConstraint)
			r1CS.R = append(r1CS.R, bConstraint)
			r1CS.E = append(r1CS.E, eConstraint)
			r1CS.O = append(r1CS.O, cConstraint)

		} else if g.gateType == egate {
			aConstraint := fields.ArrayOfBigZeros(size)
			bConstraint := fields.ArrayOfBigZeros(size)
			eConstraint := fields.ArrayOfBigZeros(size)
			cConstraint := fields.ArrayOfBigZeros(size)

			for _, val := range g.expoIns {
				insertValue(val, eConstraint)
			}

			cConstraint[indexMap[g.value.identifier]] = big.NewInt(int64(1))

			//if g.value.invert {
			//	panic("not a m Gate")
			//}
			r1CS.L = append(r1CS.L, aConstraint)
			r1CS.R = append(r1CS.R, bConstraint)
			r1CS.E = append(r1CS.E, eConstraint)
			r1CS.O = append(r1CS.O, cConstraint)

		} else {
			panic("not a m Gate")
		}
	}

	return
}
