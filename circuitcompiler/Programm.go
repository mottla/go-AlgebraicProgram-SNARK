package circuitcompiler

import (
	"crypto/sha256"
	"fmt"
	"github.com/mottla/go-AlgebraicProgram-SNARK/circuitcompiler/fields"
	"math/big"
)

type MultiplicationGateSignature struct {
	identifier      Token
	commonExtracted [2]int //if the mgate had a extractable factor, it will be stored here
}

type Program struct {
	functions    map[string]*Circuit
	globalInputs []*Gate
	Fields       fields.Fields //find a better name

	//key 1: the hash chain indicating from where the variable is called H( H(main(a,b)) , doSomething(x,z) ), where H is a hash function.
	//value 1 : map
	//			with key variable name
	//			with value variable name + hash Chain
	//this datastructure is nice but maybe ill replace it later with something less confusing
	//it serves the elementary purpose of not computing a variable a second time.
	//it boosts parse time
	computedInContext map[string]map[Token]MultiplicationGateSignature

	//to reduce the number of multiplication gates, we store each factor signature, and the variable name,
	//so each time a variable is computed, that happens to have the very same factors, we reuse the former
	//it boost setup and proof time
	computedFactors map[Token]MultiplicationGateSignature
}

func NewProgram(CurveOrder, FieldOrder *big.Int) (program *Program) {
	program = &Program{
		functions: map[string]*Circuit{},
		globalInputs: []*Gate{{value: &Constraint{Output: Token{
			Type:  NumberToken,
			Value: "1",
		}}}},
		Fields: fields.PrepareFields(CurveOrder, FieldOrder),
	}
	//pointMultiplicationCircuit := program.registerFunctionFromConstraint(&Constraint{Out: "g(x)"})
	//expGate := &Gate{gateType: egate, value: pointMultiplicationCircuit.Inputs[0].value}
	//pointMultiplicationCircuit.root = expGate
	return
}

//returns the cardinality of all main inputs + 1 for the "one" signal
func (p *Program) GlobalInputCount() int {
	return len(p.globalInputs)
}

func (p *Program) ReduceCombinedTree() (orderedmGates []*Gate) {
	orderedmGates = []*Gate{}
	p.computedInContext = make(map[string]map[Token]MultiplicationGateSignature)
	p.computedFactors = make(map[Token]MultiplicationGateSignature)
	rootHash := make([]byte, 10)
	p.computedInContext[string(rootHash)] = make(map[Token]MultiplicationGateSignature)
	for _, root := range p.getMainCircuit().rootConstraints {
		p.build(p.getMainCircuit(), root, rootHash, &orderedmGates, false, false)
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

	if newContext, v := p.functions[constraint.Output.Value]; v {

		if len(newContext.Inputs) != len(constraint.Inputs) {
			panic("argument size missmatch")
		}

		for i, _ := range newContext.Inputs {
			*newContext.Inputs[i] = *constraint.Inputs[i]
			//newContext.Inputs[i].gateType = constraint.Inputs[i].gateType
			//newContext.Inputs[i].value = constraint.Inputs[i].value
			//newContext.Inputs[i].right = constraint.Inputs[i].right
			//
			//newContext.Inputs[i].left = constraint.Inputs[i].left
			//newContext.Inputs[i].expoIns = constraint.Inputs[i].expoIns
			//newContext.Inputs[i].leftIns = constraint.Inputs[i].leftIns
			//newContext.Inputs[i].rightIns = constraint.Inputs[i].rightIns
			//*newContext.Inputs[i] = *constraint.Inputs[i]
		}

		return newContext
	}
	panic("undeclared function call. check your source")
	return nil
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

// GenerateR1CS generates the ER1CS polynomials from the Circuit
func (p *Program) GatesToR1CS(mGates []*Gate) (r1CS ER1CS) {
	// from flat code to ER1CS

	offset := len(p.globalInputs)
	//  one + in1 +in2+... + gate1 + gate2 .. + out
	size := offset + len(mGates)
	indexMap := make(map[Token]int)

	for i, v := range p.globalInputs {
		indexMap[v.value.Output] = i
	}

	for _, v := range mGates {
		if _, ex := indexMap[v.value.Output]; !ex {
			indexMap[v.value.Output] = len(indexMap)
		}
	}

	insertValue := func(val *factor, arr []*big.Int) {
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
			cConstraint[indexMap[g.value.Output]] = big.NewInt(int64(1))
			//if g.value.invert {
			//	tmp := aConstraint
			//	aConstraint = cConstraint
			//	cConstraint = tmp
			//}
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

			cConstraint[indexMap[g.value.Output]] = big.NewInt(int64(1))

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

var hasher = sha256.New()

func hashTogether(a, b []byte) []byte {
	hasher.Reset()
	hasher.Write(a)
	hasher.Write(b)
	return hasher.Sum(nil)
}
