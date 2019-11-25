package circuitcompiler

import (
	"crypto/sha256"
	"fmt"
	"github.com/mottla/go-AlgebraicProgram-SNARK/circuitcompiler/fields"
	"math/big"
	"strings"
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
	//computedInContext map[string]map[Token]MultiplicationGateSignature

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

	//p.computedInContext = make(map[string]map[Token]MultiplicationGateSignature)
	p.computedFactors = make(map[Token]MultiplicationGateSignature)
	//rootHash := make([]byte, 10)
	//p.computedInContext[string(rootHash)] = make(map[Token]MultiplicationGateSignature)
	//TODO handle multiple returns
	for _, root := range p.getMainCircuit().rootConstraints {
		if len(p.getMainCircuit().rootConstraints) > 1 {
			panic("no supported yet")
		}
		facs, _ := p.build(p.getMainCircuit(), root, &orderedmGates, false, false)
		//since we extract coefficients and hold em back as long as possible, we have to multiply them back in when the main programm exits
		//i case the retrun ends with addition, the addition will not add another gate, since its summands have been prooven already
		//this will cause confusion so we may add the unnecessary addition at some point.
		orderedmGates[len(orderedmGates)-1].leftIns = mulFactors(orderedmGates[len(orderedmGates)-1].leftIns, factors{factor{
			typ: Token{
				Type: NumberToken,
			},
			multiplicative: facs[0].multiplicative},
		})
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
		newCircut.returnConstraints[0].Output.Value = constraint.Output.Value

		return newCircut
	}
	panic("undeclared function call. check your source")
	return nil
}

//recursively walks through the parse tree to create a list of all
//multiplication gates needed for the QAP construction
//Takes into account, that multiplication with constants and addition (= substraction) can be reduced, and does so
func (p *Program) build(currentCircuit *Circuit, currentConstraint *Constraint, orderedmGates *[]*Gate, negate bool, invert bool) (facs factors, variableEnd bool) {

	if len(currentConstraint.Inputs) == 0 {
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
		nextCircuit := p.changeInputs(currentConstraint)
		//hashTraceBuildup = hashTogether(hashTraceBuildup, []byte(nextCircuit.currentOutputName()))
		//TODO think about this
		//for _, v := range nextCircuit.rootConstraints {
		//	p.build(nextCircuit, v, hashTraceBuildup, orderedmGates, false, false)
		//}
		//p.computedInContext[string(hashTraceBuildup)] = make(map[Token]MultiplicationGateSignature)
		//TODO handle multiple roots
		return p.build(nextCircuit, nextCircuit.returnConstraints[0], orderedmGates, negate, invert)
	}

	if len(currentConstraint.Inputs) == 1 {
		switch currentConstraint.Output.Type {
		case VAR:
			return p.build(currentCircuit, currentConstraint.Inputs[0], orderedmGates, negate, invert)
		case RETURN:
			return p.build(currentCircuit, currentConstraint.Inputs[0], orderedmGates, negate, invert)
		case UNASIGNEDVAR:
			return p.build(currentCircuit, currentConstraint.Inputs[0], orderedmGates, negate, invert)
		default:
			panic("")
		}
	}

	if len(currentConstraint.Inputs) == 3 {

		left := currentConstraint.Inputs[1]
		right := currentConstraint.Inputs[2]
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
				leftFactors, variableAtLeftEnd := p.build(currentCircuit, left, orderedmGates, Xor(negate, false), invert)
				rightFactors, variableAtRightEnd := p.build(currentCircuit, right, orderedmGates, Xor(negate, false), invert)
				return addFactors(leftFactors, rightFactors), variableAtLeftEnd || variableAtRightEnd
			case "/":
				leftFactors, variableAtLeftEnd = p.build(currentCircuit, left, orderedmGates, negate, false)
				rightFactors, variableAtRightEnd = p.build(currentCircuit, right, orderedmGates, negate, true)
				break out
			case "-":
				leftFactors, variableAtLeftEnd := p.build(currentCircuit, left, orderedmGates, Xor(negate, false), invert)
				rightFactors, variableAtRightEnd := p.build(currentCircuit, right, orderedmGates, Xor(negate, true), invert)
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
		//out := currentConstraint.Output.Value
		rootGate := &Gate{
			gateType: mgate,
			index:    len(*orderedmGates),
			value:    currentConstraint.Output,
			leftIns:  newLef,
			rightIns: newRigh,
		}

		p.computedFactors[sig.identifier] = MultiplicationGateSignature{identifier: currentConstraint.Output, commonExtracted: sig.commonExtracted}
		*orderedmGates = append(*orderedmGates, rootGate)

		return factors{{typ: currentConstraint.Output, invert: invert, negate: negate, multiplicative: sig.commonExtracted}}, true
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
		if _, ex := indexMap[v.value]; !ex {
			indexMap[v.value] = len(indexMap)
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
			cConstraint[indexMap[g.value]] = big.NewInt(int64(1))
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

			cConstraint[indexMap[g.value]] = big.NewInt(int64(1))

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
