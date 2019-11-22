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
	globalInputs []Token
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
		functions:    map[string]*Circuit{},
		globalInputs: []Token{},
		Fields:       fields.PrepareFields(CurveOrder, FieldOrder),
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

func (p *Program) ReduceCombinedTree(functions map[string]*Circuit) (orderedmGates []*Gate) {
	p.functions = functions
	orderedmGates = []*Gate{}
	p.globalInputs = append(p.globalInputs, Token{
		Type:  NumberToken,
		Value: "1",
	})
	for _, rootC := range p.getMainCircuit().Inputs {
		p.globalInputs = append(p.globalInputs, rootC.Output)
	}

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

	if newCircut, v := p.functions[constraint.Output.Value]; v {

		if len(newCircut.Inputs) != len(constraint.Inputs) {
			panic("argument size missmatch")
		}

		for i, _ := range newCircut.Inputs {
			*newCircut.Inputs[i] = *constraint.Inputs[i]
		}
		return newCircut
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
		hashTraceBuildup = hashTogether(hashTraceBuildup, []byte(nextCircuit.currentOutputName()))
		//TODO think about this
		//for _, v := range nextCircuit.rootConstraints {
		//	p.build(nextCircuit, v, hashTraceBuildup, orderedmGates, false, false)
		//}
		p.computedInContext[string(hashTraceBuildup)] = make(map[Token]MultiplicationGateSignature)
		//TODO handle multiple roots
		return p.build(nextCircuit, nextCircuit.returnConstraints[0], hashTraceBuildup, orderedmGates, negate, invert)
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

			return factors{{typ: currentConstraint.Output, negate: negate, multiplicative: mul}}, hashTraceBuildup, false
		case IdentToken:
			if con, ex := currentCircuit.constraintMap[currentConstraint.Output.Value]; ex {
				return p.build(currentCircuit, con, hashTraceBuildup, orderedmGates, negate, invert)
			}
			panic("asdf")
		case UNASIGNEDVAR:
			if con, ex := currentCircuit.constraintMap[currentConstraint.Output.Value]; ex {
				return p.build(currentCircuit, con, hashTraceBuildup, orderedmGates, negate, invert)
			}
			panic("asdf")
		case RETURN:
			fac := &factor{typ: Token{
				Type:  NumberToken,
				Value: "1",
			}, negate: negate, multiplicative: [2]int{1, 1}}
			return factors{fac}, hashTraceBuildup, false
		case ARGUMENT:
			fac := &factor{typ: Token{
				Type:  IdentToken,
				Value: currentConstraint.Output.Value, //+string(hashTraceBuildup),
			}, negate: negate, invert: invert, multiplicative: [2]int{1, 1}}
			return factors{fac}, hashTraceBuildup, true
		default:
			panic("")
		}
	}

	if len(currentConstraint.Inputs) == 1 {
		switch currentConstraint.Output.Type {
		case VAR:
			return p.build(currentCircuit, currentConstraint.Inputs[0], hashTraceBuildup, orderedmGates, negate, invert)
		case RETURN:
			return p.build(currentCircuit, currentConstraint.Inputs[0], hashTraceBuildup, orderedmGates, negate, invert)
		case UNASIGNEDVAR:
			return p.build(currentCircuit, currentConstraint.Inputs[0], hashTraceBuildup, orderedmGates, negate, invert)
		default:
			panic("")
		}
	}

	if len(currentConstraint.Inputs) == 3 {

		left := currentConstraint.Inputs[1]
		right := currentConstraint.Inputs[2]
		operation := currentConstraint.Inputs[0].Output

		leftFactors, hl, variableAtLeftEnd := p.build(currentCircuit, left, hashTraceBuildup, orderedmGates, negate, invert)
		rightFactors, hr, variableAtRightEnd := p.build(currentCircuit, right, hashTraceBuildup, orderedmGates, Xor(negate, false), invert)

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

				out := currentConstraint.Output.Value + string(hashTogether(hl, hr)[:10])
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
			case "+":
				return addFactors(leftFactors, rightFactors), hashTraceBuildup, variableAtLeftEnd || variableAtRightEnd
			}
			break
		case AssignmentOperatorToken:
			break
		default:
			panic("")
		}
	}
	fmt.Println("asdf")
	panic(currentConstraint)
}

// GenerateR1CS generates the ER1CS polynomials from the Circuit
func (p *Program) GatesToR1CS(mGates []*Gate) (r1CS ER1CS) {
	// from flat code to ER1CS

	offset := len(p.globalInputs)
	//  one + in1 +in2+... + gate1 + gate2 .. + out
	size := offset + len(mGates)
	indexMap := make(map[string]int)

	for i, v := range p.globalInputs {
		indexMap[v.Value] = i
	}

	for _, v := range mGates {
		if _, ex := indexMap[v.value.Output.Value]; !ex {
			indexMap[v.value.Output.Value] = len(indexMap)
		}
	}

	insertValue := func(val *factor, arr []*big.Int) {
		if val.typ.Type != NumberToken {
			if _, ex := indexMap[val.typ.Value]; !ex {
				panic(fmt.Sprintf("%v index not found!!!", val))
			}
		}
		value := p.Fields.ArithmeticField.FractionToField(val.multiplicative)
		if val.negate {
			value = p.Fields.ArithmeticField.Neg(value)
		}
		//not that index is 0 if its a constant, since 0 is the map default if no entry was found
		arr[indexMap[val.typ.Value]] = value
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
			cConstraint[indexMap[g.value.Output.Value]] = big.NewInt(int64(1))
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

			cConstraint[indexMap[g.value.Output.Value]] = big.NewInt(int64(1))

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
