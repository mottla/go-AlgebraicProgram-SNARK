package circuitcompiler

import (
	"fmt"
	"github.com/mottla/go-AlgebraicProgram-SNARK/utils"
	"math/big"
	"sort"
)

type MultiplicationGateSignature struct {
	identifier      Token
	commonExtracted *big.Int //if the multiplicationGate had a extractable factor, it will be stored here
}

func (m MultiplicationGateSignature) String() string {
	return fmt.Sprintf("%s extracted %v", m.identifier.String(), m.commonExtracted)
}

type Program struct {
	functions    map[string]*Circuit
	GlobalInputs []Token
	Fields       utils.Fields //find a better name
	//to reduce the number of multiplication gates, we store each factor signature, and the variable name,
	//so each time a variable is computed, that happens to have the very same factors, we reuse the former
	//it boost setup and proof time
	computedFactors map[Token]MultiplicationGateSignature
}

func newProgram(CurveOrder, FieldOrder *big.Int) (program *Program) {

	program = &Program{
		//functions:    map[string]*Circuit{"scalarBaseMultiply": G, "equal": E},
		functions:    map[string]*Circuit{},
		GlobalInputs: []Token{},
		Fields:       utils.PrepareFields(CurveOrder, FieldOrder),
	}

	return
}

type InputArgument struct {
	identifier string
	value      *big.Int
}

func (in InputArgument) String() string {
	return fmt.Sprintf("(%v,%v)", in.identifier, in.value.String())
}

func CombineInputs(abstract []Token, concrete []*big.Int) (res []InputArgument) {
	if len(abstract) != len(concrete) {
		panic("argument missmatch")
	}
	if len(abstract) == 0 {
		return
	}
	res = make([]InputArgument, len(abstract))

	for k, v := range abstract {
		res[k] = InputArgument{identifier: v.Identifier, value: concrete[k]}
	}

	return res
}

//returns the cardinality of all main inputs + 1 for the "one" signal
func (p *Program) GlobalInputCount() int {
	return len(p.GlobalInputs)
}

func (p *Program) ReduceCombinedTree() (orderedmGates []*Gate) {

	orderedmGates = []*Gate{}

	for _, rootC := range p.getMainCircuit().Inputs {
		p.GlobalInputs = append(p.GlobalInputs, rootC.Output)
	}

	p.computedFactors = make(map[Token]MultiplicationGateSignature)

	mainCircuit := p.getMainCircuit()

	for i := 0; i < mainCircuit.rootConstraints.len(); i++ {
		f, _ := p.compile(mainCircuit, mainCircuit.rootConstraints.data[i], &orderedmGates)
		fmt.Println(f)
		for _, fac := range f {
			for k := range orderedmGates {
				if orderedmGates[k].value.identifier.Identifier == fac.typ.Identifier {
					orderedmGates[k].output = p.Fields.ArithmeticField.Inverse(fac.multiplicative)
				}
			}
		}
	}
	return orderedmGates
}

func (p *Program) getMainCircuit() *Circuit {
	return p.functions["main"]
}

func (p *Program) rereferenceFunctionInputs(currentCircuit *Circuit, functionName string, newInputs []*Constraint) (oldInputs []*Constraint, nextContext *Circuit) {

	//first we check if the function is defined internally
	if newCircut, v := currentCircuit.functions[functionName]; v {
		if len(newCircut.Inputs) != len(newInputs) {
			panic("argument size missmatch")
		}
		oldInputss := make([]*Constraint, len(newCircut.Inputs))
		for i, _ := range newCircut.Inputs {
			oldInputss[i] = newCircut.Inputs[i].clone()
			*newCircut.Inputs[i] = *newInputs[i]
		}
		return oldInputss, newCircut

	}

	//now we check if its defined externally. maybe we remove this when we make the program a circuit too.
	if newCircut, v := p.functions[functionName]; v {

		if len(newCircut.Inputs) != len(newInputs) {
			panic("argument size missmatch")
		}
		oldInputss := make([]*Constraint, len(newCircut.Inputs))
		for i, _ := range newCircut.Inputs {
			oldInputss[i] = newCircut.Inputs[i].clone()
			*newCircut.Inputs[i] = *newInputs[i]

		}

		return oldInputss, newCircut
	}
	panic("undeclared function call. check your source")
	return nil, nil
}

//func (p *Program) rebalanceAVL(currentCircuit *Circuit, currentConstraint *Constraint) (weight int) {
//
//	if len(currentConstraint.Inputs) == 0 {
//		return 1
//	}
//
//	if currentConstraint.Output.Type == FUNCTION_CALL {
//		switch currentConstraint.Output.Identifier {
//		case "scalarBaseMultiply":
//
//			return 1
//		case "equal":
//			return 1
//		default:
//			oldInputss, nextCircuit := p.rereferenceFunctionInputs(currentCircuit, currentConstraint.Output.Identifier, currentConstraint.Inputs)
//
//			for i := 0; i < nextCircuit.rootConstraints.len()-1; i++ {
//				p.rebalanceAVL(nextCircuit, nextCircuit.rootConstraints.data[i])
//			}
//
//			v := p.rebalanceAVL(nextCircuit, nextCircuit.rootConstraints.data[nextCircuit.rootConstraints.len()-1])
//			p.rereferenceFunctionInputs(currentCircuit, currentConstraint.Output.Identifier, oldInputss)
//			return v
//		}
//
//	}
//	if currentConstraint.Output.Type == ARRAY_CALL {
//
//		indexFactors, variable := p.compile(currentCircuit, currentConstraint.Inputs[0], &[]*Gate{})
//		if variable {
//			panic("cannot access array dynamically in an arithmetic circuit currently")
//		}
//
//		elementName := fmt.Sprintf("%s[%v]", currentConstraint.Output.Identifier, indexFactors[0].multiplicative.String())
//		if con, ex := currentCircuit.constraintMap[elementName]; ex {
//			return p.rebalanceAVL(currentCircuit, con)
//		}
//		panic(fmt.Sprintf("entry %v not found", elementName))
//	}
//
//	if len(currentConstraint.Inputs) == 1 {
//		switch currentConstraint.Output.Type {
//		case VARIABLE_DECLARE:
//			return p.rebalanceAVL(currentCircuit, currentConstraint.Inputs[0])
//		case RETURN:
//			return p.rebalanceAVL(currentCircuit, currentConstraint.Inputs[0])
//		case UNASIGNEDVAR:
//			return p.rebalanceAVL(currentCircuit, currentConstraint.Inputs[0])
//		case IdentToken:
//			return p.rebalanceAVL(currentCircuit, currentConstraint.Inputs[0])
//		case VARIABLE_OVERLOAD:
//			return p.rebalanceAVL(currentCircuit, currentConstraint.Inputs[0])
//		default:
//			panic(currentConstraint.String())
//		}
//	}
//
//	if len(currentConstraint.Inputs) == 3 {
//
//		left := currentConstraint.Inputs[1]
//		right := currentConstraint.Inputs[2]
//		operation := currentConstraint.Inputs[0].Output
//
//		switch operation.Type {
//		case BinaryComperatorToken:
//			break
//		case BitOperatorToken:
//			break
//		case BooleanOperatorToken:
//			break
//		case ArithmeticOperatorToken:
//			switch operation.Identifier {
//			case "*":
//				variableAtLeftEnd = p.rebalanceAVL(currentCircuit, left)
//				 variableAtRightEnd = p.rebalanceAVL(currentCircuit, right)
//				break
//			case "+":
//				leftFactors, variableAtLeftEnd = p.compile(currentCircuit, left, orderedmGates)
//				rightFactors, variableAtRightEnd = p.compile(currentCircuit, right, orderedmGates)
//				return addFactors(leftFactors, rightFactors), variableAtLeftEnd || variableAtRightEnd
//			case "/":
//				leftFactors, variableAtLeftEnd = p.compile(currentCircuit, left, orderedmGates)
//				rightFactors, variableAtRightEnd = p.compile(currentCircuit, right, orderedmGates)
//				rightFactors = invertFactors(rightFactors)
//				break
//			case "-":
//				leftFactors, variableAtLeftEnd = p.compile(currentCircuit, left, orderedmGates)
//				rightFactors, variableAtRightEnd = p.compile(currentCircuit, right, orderedmGates)
//				rightFactors = negateFactors(rightFactors)
//				return addFactors(leftFactors, rightFactors), variableAtLeftEnd || variableAtRightEnd
//			}
//			break
//		case AssignmentOperatorToken:
//			break
//		default:
//			panic("unsupported operation")
//		}
//
//		if !(variableAtLeftEnd && variableAtRightEnd) {
//			return mulFactors(leftFactors, rightFactors), variableAtLeftEnd || variableAtRightEnd
//		}
//		sig, newLef, newRigh := extractConstant(leftFactors, rightFactors)
//		if out, ex := p.computedFactors[sig.identifier]; ex {
//			return factors{{typ: out.identifier, multiplicative: sig.commonExtracted}}, true
//		}
//		//currentConstraint.Output.Identifier += "@"
//		//currentConstraint.Output.Identifier += sig.identifier.Identifier
//		nTok := Token{
//			Type: currentConstraint.Output.Type,
//			//Identifier: currentConstraint.Output.Identifier + "@" + sig.identifier.Identifier,
//			Identifier: sig.identifier.Identifier,
//		}
//		rootGate := &Gate{
//			gateType: multiplicationGate,
//			index:    len(*orderedmGates),
//			value:    MultiplicationGateSignature{identifier: nTok, commonExtracted: sig.commonExtracted},
//			leftIns:  newLef,
//			rightIns: newRigh,
//			output:   big.NewInt(int64(1)),
//		}
//
//		p.computedFactors[sig.identifier] = MultiplicationGateSignature{identifier: nTok, commonExtracted: sig.commonExtracted}
//		*orderedmGates = append(*orderedmGates, rootGate)
//
//		return factors{{typ: nTok, multiplicative: sig.commonExtracted}}, true
//	}
//
//	panic(currentConstraint)
//}

//recursively walks through the parse tree to create a list of all
//multiplication gates needed for the QAP construction
//Takes into account, that multiplication with constants and addition (= substraction) can be reduced, and does so
func (p *Program) compile(currentCircuit *Circuit, currentConstraint *Constraint, orderedmGates *[]*Gate) (facs factors, variableEnd bool) {

	if len(currentConstraint.Inputs) == 0 {
		switch currentConstraint.Output.Type {
		case NumberToken:

			value, success := p.Fields.ArithmeticField.StringToFieldElement(currentConstraint.Output.Identifier)
			if !success {
				panic("not a constant")
			}
			return factors{{typ: Token{Type: NumberToken}, multiplicative: value}}, false
		case IdentToken:
			if con, ex := currentCircuit.constraintMap[currentConstraint.Output.Identifier]; ex {
				return p.compile(currentCircuit, con, orderedmGates)
			}
			panic("asdf")
		case UNASIGNEDVAR:
			if con, ex := currentCircuit.constraintMap[currentConstraint.Output.Identifier]; ex {
				return p.compile(currentCircuit, con, orderedmGates)
			}
			panic("asdf")
		case RETURN:
			//panic("empty return not implemented yet")
			fac := &factor{typ: Token{
				Type: NumberToken,
			}, multiplicative: big.NewInt(1)}
			return factors{fac}, false
		case ARGUMENT:
			fac := &factor{typ: Token{
				Type:       ARGUMENT,
				Identifier: currentConstraint.Output.Identifier, //+string(hashTraceBuildup),
			}, multiplicative: big.NewInt(1)}
			return factors{fac}, true
		default:
			panic("")
		}
	}

	if currentConstraint.Output.Type == FUNCTION_CALL {
		switch currentConstraint.Output.Identifier {
		case "scalarBaseMultiply":
			if len(currentConstraint.Inputs) != 1 {
				panic("scalarBaseMultiply argument missmatch")
			}
			secretFactors, _ := p.compile(currentCircuit, currentConstraint.Inputs[0], orderedmGates)

			sort.Sort(secretFactors)
			sig := hashToBig(secretFactors).String()[:16]

			nTok := Token{
				Type:       FUNCTION_CALL,
				Identifier: sig,
			}
			if _, ex := p.computedFactors[nTok]; !ex {
				rootGate := &Gate{
					gateType: scalarBaseMultiplyGate,
					index:    len(*orderedmGates),
					value:    MultiplicationGateSignature{identifier: nTok, commonExtracted: bigOne},
					expoIns:  secretFactors,
					output:   bigOne,
				}
				p.computedFactors[nTok] = rootGate.value
				*orderedmGates = append(*orderedmGates, rootGate)
			}

			return factors{&factor{
				typ:            nTok,
				multiplicative: bigOne,
			}}, true
		case "equal":
			if len(currentConstraint.Inputs) != 2 {
				panic("equality constraint requires 2 arguments")
			}
			leftClone := currentConstraint.Inputs[0].clone()
			rightClone := currentConstraint.Inputs[1].clone()
			l, _ := p.compile(currentCircuit, leftClone, orderedmGates)
			r, _ := p.compile(currentCircuit, rightClone, orderedmGates)
			sort.Sort(l)
			sort.Sort(r)
			hl := hashToBig(l)
			hr := hashToBig(r)
			//this way equal(a,b) = equal(b,a). collision is unlikely but possible
			sig := new(big.Int).Add(hl, hr).String()[:16]

			nTok := Token{
				Type:       FUNCTION_CALL,
				Identifier: sig,
			}
			if _, ex := p.computedFactors[nTok]; !ex {
				rootGate := &Gate{
					gateType: equalityGate,
					index:    len(*orderedmGates),
					value:    MultiplicationGateSignature{identifier: nTok, commonExtracted: bigOne},
					leftIns:  l,
					rightIns: r,
					output:   bigOne,
				}
				p.computedFactors[nTok] = rootGate.value
				*orderedmGates = append(*orderedmGates, rootGate)
			}

			return factors{&factor{
				typ:            nTok,
				multiplicative: bigOne,
			}}, true
			return
		default:
			oldInputss, nextCircuit := p.rereferenceFunctionInputs(currentCircuit, currentConstraint.Output.Identifier, currentConstraint.Inputs)

			for i := 0; i < nextCircuit.rootConstraints.len()-1; i++ {
				f, _ := p.compile(nextCircuit, nextCircuit.rootConstraints.data[i], orderedmGates)
				for _, fac := range f {
					for k := range *orderedmGates {
						if (*orderedmGates)[k].value.identifier.Identifier == fac.typ.Identifier {
							(*orderedmGates)[k].output = p.Fields.ArithmeticField.Inverse(fac.multiplicative)
						}
					}
				}
			}

			facss, varEnd := p.compile(nextCircuit, nextCircuit.rootConstraints.data[nextCircuit.rootConstraints.len()-1], orderedmGates)
			p.rereferenceFunctionInputs(currentCircuit, currentConstraint.Output.Identifier, oldInputss)
			return facss, varEnd
		}

	}
	if currentConstraint.Output.Type == ARRAY_CALL {

		if len(currentConstraint.Inputs) != 1 {
			panic("scalarBaseMultiply argument missmatch")
		}
		indexFactors, variable := p.compile(currentCircuit, currentConstraint.Inputs[0], orderedmGates)
		if variable {
			panic("cannot access array dynamically in an arithmetic circuit currently")
		}
		if len(facs) > 1 {
			panic("unexpected")
		}
		elementName := fmt.Sprintf("%s[%v]", currentConstraint.Output.Identifier, indexFactors[0].multiplicative.String())
		if con, ex := currentCircuit.constraintMap[elementName]; ex {
			return p.compile(currentCircuit, con, orderedmGates)
		}
		panic(fmt.Sprintf("entry %v not found", elementName))
	}

	if len(currentConstraint.Inputs) == 1 {
		switch currentConstraint.Output.Type {
		case VARIABLE_DECLARE:
			return p.compile(currentCircuit, currentConstraint.Inputs[0], orderedmGates)
		case RETURN:
			return p.compile(currentCircuit, currentConstraint.Inputs[0], orderedmGates)
		case UNASIGNEDVAR:
			return p.compile(currentCircuit, currentConstraint.Inputs[0], orderedmGates)
		case IdentToken:
			return p.compile(currentCircuit, currentConstraint.Inputs[0], orderedmGates)
		case VARIABLE_OVERLOAD:
			return p.compile(currentCircuit, currentConstraint.Inputs[0], orderedmGates)
		default:
			panic(currentConstraint.String())
		}
	}

	if len(currentConstraint.Inputs) == 3 {

		left := currentConstraint.Inputs[1]
		right := currentConstraint.Inputs[2]
		operation := currentConstraint.Inputs[0].Output
		var leftFactors, rightFactors factors
		var variableAtLeftEnd, variableAtRightEnd bool

		switch operation.Type {
		case BinaryComperatorToken:
			break
		case BitOperatorToken:
			break
		case BooleanOperatorToken:
			break
		case ArithmeticOperatorToken:
			switch operation.Identifier {
			case "*":
				leftFactors, variableAtLeftEnd = p.compile(currentCircuit, left, orderedmGates)
				rightFactors, variableAtRightEnd = p.compile(currentCircuit, right, orderedmGates)
				break
			case "+":
				leftFactors, variableAtLeftEnd = p.compile(currentCircuit, left, orderedmGates)
				rightFactors, variableAtRightEnd = p.compile(currentCircuit, right, orderedmGates)
				return addFactors(leftFactors, rightFactors), variableAtLeftEnd || variableAtRightEnd
			case "/":
				leftFactors, variableAtLeftEnd = p.compile(currentCircuit, left, orderedmGates)
				rightFactors, variableAtRightEnd = p.compile(currentCircuit, right, orderedmGates)
				rightFactors = invertFactors(rightFactors)
				break
			case "-":
				leftFactors, variableAtLeftEnd = p.compile(currentCircuit, left, orderedmGates)
				rightFactors, variableAtRightEnd = p.compile(currentCircuit, right, orderedmGates)
				rightFactors = negateFactors(rightFactors)
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
		sig, newLef, newRigh := extractConstant(leftFactors, rightFactors)
		if out, ex := p.computedFactors[sig.identifier]; ex {
			return factors{{typ: out.identifier, multiplicative: sig.commonExtracted}}, true
		}
		//currentConstraint.Output.Identifier += "@"
		//currentConstraint.Output.Identifier += sig.identifier.Identifier
		nTok := Token{
			Type: currentConstraint.Output.Type,
			//Identifier: currentConstraint.Output.Identifier + "@" + sig.identifier.Identifier,
			Identifier: sig.identifier.Identifier,
		}
		rootGate := &Gate{
			gateType: multiplicationGate,
			index:    len(*orderedmGates),
			value:    MultiplicationGateSignature{identifier: nTok, commonExtracted: sig.commonExtracted},
			leftIns:  newLef,
			rightIns: newRigh,
			output:   big.NewInt(int64(1)),
		}

		p.computedFactors[sig.identifier] = MultiplicationGateSignature{identifier: nTok, commonExtracted: sig.commonExtracted}
		*orderedmGates = append(*orderedmGates, rootGate)

		return factors{{typ: nTok, multiplicative: sig.commonExtracted}}, true
	}

	panic(currentConstraint)
}

// GenerateR1CS generates the ER1CS polynomials from the Circuit
func (p *Program) GatesToR1CS(mGates []*Gate) (r1CS *ER1CS) {
	// from flat code to ER1CS
	r1CS = &ER1CS{
		F: p.Fields,
	}
	neutralElement := "1"

	//offset := len(p.GlobalInputs) + 2
	//  one + in1 +in2+... + gate1 + gate2 .. + randIn + randOut
	//size := offset + len(mGates)
	indexMap := make(map[string]int)
	r1CS.indexMap = indexMap
	indexMap[neutralElement] = len(indexMap)
	for _, v := range p.GlobalInputs {
		indexMap[v.Identifier] = len(indexMap)
	}

	for _, v := range mGates {
		if v.gateType == equalityGate {
			//size = size - 1
			continue
		}
		if _, ex := indexMap[v.value.identifier.Identifier]; !ex {
			indexMap[v.value.identifier.Identifier] = len(indexMap)
		} else {
			panic(fmt.Sprintf("rewriting %v ", v.value))
		}
	}
	indexMap[randInput] = len(indexMap)
	indexMap[randOutput] = len(indexMap)

	insertValue := func(val *factor, arr []*big.Int) {
		if val.typ.Type != NumberToken {
			if _, ex := indexMap[val.typ.Identifier]; !ex {
				panic(fmt.Sprintf("%v index not found!!!", val))
			}
		}
		value := val.multiplicative
		//not that index is 0 if its a constant, since 0 is the map default if no entry was found
		arr[indexMap[val.typ.Identifier]] = value
	}
	size := len(indexMap)
	for _, g := range mGates {

		switch g.gateType {
		case multiplicationGate:
			aConstraint := utils.ArrayOfBigZeros(size)
			bConstraint := utils.ArrayOfBigZeros(size)
			eConstraint := utils.ArrayOfBigZeros(size)
			cConstraint := utils.ArrayOfBigZeros(size)

			for _, val := range g.leftIns {
				insertValue(val, aConstraint)
			}

			for _, val := range g.rightIns {
				insertValue(val, bConstraint)
			}
			cConstraint[indexMap[g.value.identifier.Identifier]] = g.output

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
			break
		case scalarBaseMultiplyGate:
			aConstraint := utils.ArrayOfBigZeros(size)
			bConstraint := utils.ArrayOfBigZeros(size)
			eConstraint := utils.ArrayOfBigZeros(size)
			cConstraint := utils.ArrayOfBigZeros(size)

			for _, val := range g.expoIns {
				insertValue(val, eConstraint)
			}

			cConstraint[indexMap[g.value.identifier.Identifier]] = big.NewInt(int64(1))

			r1CS.L = append(r1CS.L, aConstraint)
			r1CS.R = append(r1CS.R, bConstraint)
			r1CS.E = append(r1CS.E, eConstraint)
			r1CS.O = append(r1CS.O, cConstraint)
			break
		case equalityGate:
			aConstraint := utils.ArrayOfBigZeros(size)
			bConstraint := utils.ArrayOfBigZeros(size)
			eConstraint := utils.ArrayOfBigZeros(size)
			cConstraint := utils.ArrayOfBigZeros(size)

			for _, val := range g.leftIns {
				insertValue(val, aConstraint)
			}

			for _, val := range g.rightIns {
				insertValue(val, cConstraint)
			}

			bConstraint[0] = big.NewInt(int64(1))

			r1CS.L = append(r1CS.L, aConstraint)
			r1CS.R = append(r1CS.R, bConstraint)
			r1CS.E = append(r1CS.E, eConstraint)
			r1CS.O = append(r1CS.O, cConstraint)
			break
		default:
			panic("no supported gate type")

		}

	}

	//randomizer gate
	aConstraint := utils.ArrayOfBigZeros(size)
	bConstraint := utils.ArrayOfBigZeros(size)
	eConstraint := utils.ArrayOfBigZeros(size)
	cConstraint := utils.ArrayOfBigZeros(size)

	insertValue(&factor{typ: Token{Identifier: randInput}, multiplicative: bigOne}, aConstraint)
	insertValue(&factor{typ: Token{Identifier: randInput}, multiplicative: bigOne}, bConstraint)
	insertValue(&factor{typ: Token{Identifier: randInput}, multiplicative: bigOne}, eConstraint)
	insertValue(&factor{typ: Token{Identifier: randOutput}, multiplicative: bigOne}, cConstraint)

	r1CS.L = append(r1CS.L, aConstraint)
	r1CS.R = append(r1CS.R, bConstraint)
	r1CS.E = append(r1CS.E, eConstraint)
	r1CS.O = append(r1CS.O, cConstraint)

	return
}
