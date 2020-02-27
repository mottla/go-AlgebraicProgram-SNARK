package circuitcompiler

import (
	"fmt"
	"github.com/mottla/go-AlgebraicProgram-SNARK/utils"
	"math/big"
	"sort"
)

type gateContainer struct {
	orderedmGates   []*Gate
	computedFactors map[Token]MultiplicationGateSignature
}

func newGateContainer() *gateContainer {
	return &gateContainer{
		orderedmGates:   []*Gate{},
		computedFactors: make(map[Token]MultiplicationGateSignature),
	}
}

func (g *gateContainer) appendFactors(f factors) {
	for _, fac := range f {
		for _, k := range g.orderedmGates {
			if k.value.identifier.Identifier == fac.typ.Identifier {
				k.output = utils.Field.ArithmeticField.Inverse(fac.multiplicative)
			}
		}
	}
}

func (g *gateContainer) contains(tok Token) (MultiplicationGateSignature, bool) {
	val, ex := g.computedFactors[tok]
	return val, ex
}

func (g *gateContainer) Add(gate *Gate) {
	if _, ex := g.computedFactors[gate.value.identifier]; !ex {
		g.computedFactors[gate.value.identifier] = gate.value
		g.orderedmGates = append(g.orderedmGates, gate)
	}
}

type MultiplicationGateSignature struct {
	identifier      Token
	commonExtracted *big.Int //if the multiplicationGate had a extractable factor, it will be stored here
}

func (m MultiplicationGateSignature) String() string {
	return fmt.Sprintf("%s extracted %v", m.identifier.String(), m.commonExtracted)
}

type Program struct {
	globalFunction *Circuit
	GlobalInputs   []string
	//to reduce the number of multiplication gates, we store each factor signature, and the variable name,
	//so each time a variable is computed, that happens to have the very same factors, we reuse the former
	//it boost setup and proof time
	computedFactors map[Token]MultiplicationGateSignature
}

func newProgram() (program *Program) {
	program = &Program{
		globalFunction: newCircuit("global", nil),
		GlobalInputs:   []string{},
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

func CombineInputs(abstract []string, concrete []*big.Int) (res []InputArgument) {
	if len(abstract) != len(concrete) {
		panic("argument missmatch")
	}
	if len(abstract) == 0 {
		return
	}
	res = make([]InputArgument, len(abstract))

	for k, v := range abstract {
		res[k] = InputArgument{identifier: v, value: concrete[k]}
	}

	return res
}

//returns the cardinality of all main inputs + 1 for the "one" signal
func (p *Program) GlobalInputCount() int {
	return len(p.GlobalInputs)
}

func (p *Program) ReduceCombinedTree() (orderedmGates []*Gate) {

	container := newGateContainer()

	p.GlobalInputs = p.getMainCircuit().Inputs

	p.computedFactors = make(map[Token]MultiplicationGateSignature)

	mainCircuit := p.getMainCircuit()

	for i := 0; i < mainCircuit.rootConstraints.len(); i++ {
		f, _ := mainCircuit.compile(mainCircuit.rootConstraints.data[i], container)
		container.appendFactors(f)
	}
	return container.orderedmGates
}

func (p *Program) getMainCircuit() *Circuit {
	return p.globalFunction.functions["main"]
}

func (currentCircuit *Circuit) rereferenceFunctionInputs(functionName string, newInputs []*Constraint) (nextContext *Circuit) {

	//first we check if the function is defined internally
	functionThatGetsCalled, exists := currentCircuit.findFunctionInBloodline(functionName)
	if !exists {
		panic("function not declared")
	}
	if len(functionThatGetsCalled.Inputs) != len(newInputs) {
		panic("argument size missmatch")
	}
	for i, name := range functionThatGetsCalled.Inputs {
		if _, ex := functionThatGetsCalled.functions[name]; !ex {
			panic("unexpected reach")
		}
		var newFunction *Circuit

		if _, ex := currentCircuit.findFunctionInBloodline(newInputs[i].Output.Identifier); ex {
			newFunction = currentCircuit.rereferenceFunctionInputs(newInputs[i].Output.Identifier, newInputs[i].Inputs)
		} else {
			newFunction = newCircuit("tmp", currentCircuit)
			np := newInputs[i].clone()
			newFunction.updateRootsMap(np)
		}
		functionThatGetsCalled.functions[name] = newFunction
	}
	return functionThatGetsCalled

}

func (currentCircuit *Circuit) findFunctionInBloodline(identifier string) (*Circuit, bool) {
	if currentCircuit == nil {
		return nil, false
	}
	if con, ex := currentCircuit.functions[identifier]; ex {
		return con, true
	}
	return currentCircuit.Context.findFunctionInBloodline(identifier)

}

func (currentCircuit *Circuit) findConstraintInBloodline(identifier string) (*Constraint, bool) {
	if currentCircuit == nil {
		return nil, false
	}
	if con, ex := currentCircuit.constraintMap[identifier]; ex {
		return con, true
	}
	return currentCircuit.Context.findConstraintInBloodline(identifier)

}

//recursively walks through the parse tree to create a list of all
//multiplication gates needed for the QAP construction
//Takes into account, that multiplication with constants and addition (= substraction) can be reduced, and does so
func (currentCircuit *Circuit) compile(currentConstraint *Constraint, gateCollector *gateContainer) (facs factors, variableEnd bool) {

	switch currentConstraint.Output.Type {
	case NumberToken:
		switch len(currentConstraint.Inputs) {
		case 0:
			value, success := utils.Field.ArithmeticField.StringToFieldElement(currentConstraint.Output.Identifier)
			if !success {
				panic("not a constant")
			}
			return factors{{typ: Token{Type: NumberToken}, multiplicative: value}}, false
		default:
			panic(currentConstraint)
		}

	case IdentToken:
		switch len(currentConstraint.Inputs) {
		case 0:
			if con, ex := currentCircuit.constraintMap[currentConstraint.Output.Identifier]; ex {
				return currentCircuit.compile(con, gateCollector)
			}
		case 1:
			return currentCircuit.compile(currentConstraint.Inputs[0], gateCollector)
		case 3:
		default:
			panic(currentConstraint)
		}

	case UNASIGNEDVAR:
		switch len(currentConstraint.Inputs) {
		case 0:
			if con, ex := currentCircuit.constraintMap[currentConstraint.Output.Identifier]; ex {
				return currentCircuit.compile(con, gateCollector)
			}
		case 1:
			return currentCircuit.compile(currentConstraint.Inputs[0], gateCollector)
		case 3:
		default:
			panic(currentConstraint)
		}

	case RETURN:
		switch len(currentConstraint.Inputs) {
		case 0:
			fac := &factor{typ: Token{
				Type: NumberToken,
			}, multiplicative: big.NewInt(1)}
			return factors{fac}, false
		case 1:
			return currentCircuit.compile(currentConstraint.Inputs[0], gateCollector)
		case 3:
		default:
			panic(currentConstraint)
		}
	case ARGUMENT:
		fac := &factor{typ: Token{
			Type:       ARGUMENT,
			Identifier: currentConstraint.Output.Identifier, //+string(hashTraceBuildup),
		}, multiplicative: big.NewInt(1)}
		return factors{fac}, true
	case VARIABLE_DECLARE:
		switch len(currentConstraint.Inputs) {
		case 1:
			return currentCircuit.compile(currentConstraint.Inputs[0], gateCollector)
		case 3:
		default:
			panic(currentConstraint)
		}
	case VARIABLE_OVERLOAD:
		switch len(currentConstraint.Inputs) {
		case 1:
			return currentCircuit.compile(currentConstraint.Inputs[0], gateCollector)
		case 3:
		default:
			panic(currentConstraint)
		}

	case ARRAY_CALL:

		if len(currentConstraint.Inputs) != 1 {
			panic("accessing array index failed")
		}
		indexFactors, variable := currentCircuit.compile(currentConstraint.Inputs[0], gateCollector)
		if variable {
			panic("cannot access array dynamically in an arithmetic circuit currently")
		}
		if len(facs) > 1 {
			panic("unexpected")
		}

		elementName := fmt.Sprintf("%s[%v]", currentConstraint.Output.Identifier, indexFactors[0].multiplicative.String())

		if con, ex := currentCircuit.findConstraintInBloodline(elementName); ex {
			return currentCircuit.compile(con, gateCollector)
		}

		panic(fmt.Sprintf("entry %v not found", elementName))
	default:

	}

	if currentConstraint.Output.Type == FUNCTION_CALL {
		switch currentConstraint.Output.Identifier {
		case "scalarBaseMultiply":
			if len(currentConstraint.Inputs) != 1 {
				panic("scalarBaseMultiply argument missmatch")
			}
			secretFactors, _ := currentCircuit.compile(currentConstraint.Inputs[0], gateCollector)

			sort.Sort(secretFactors)
			sig := hashToBig(secretFactors).String()[:16]

			nTok := Token{
				Type:       FUNCTION_CALL,
				Identifier: sig,
			}

			rootGate := &Gate{
				gateType: scalarBaseMultiplyGate,
				value:    MultiplicationGateSignature{identifier: nTok, commonExtracted: bigOne},
				expoIns:  secretFactors,
				output:   bigOne,
			}
			gateCollector.Add(rootGate)

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
			l, _ := currentCircuit.compile(leftClone, gateCollector)
			r, _ := currentCircuit.compile(rightClone, gateCollector)
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

			rootGate := &Gate{
				gateType: equalityGate,
				value:    MultiplicationGateSignature{identifier: nTok, commonExtracted: bigOne},
				leftIns:  l,
				rightIns: r,
				output:   bigOne,
			}
			gateCollector.Add(rootGate)

			return factors{&factor{
				typ:            nTok,
				multiplicative: bigOne,
			}}, true
			return
		default:
			nextCircuit := currentCircuit.rereferenceFunctionInputs(currentConstraint.Output.Identifier, currentConstraint.Inputs)

			for i := 0; i < nextCircuit.rootConstraints.len()-1; i++ {
				f, _ := nextCircuit.compile(nextCircuit.rootConstraints.data[i], gateCollector)
				gateCollector.appendFactors(f)
			}
			//TODO why sould the last root be treated different
			facss, varEnd := nextCircuit.compile(nextCircuit.rootConstraints.data[nextCircuit.rootConstraints.len()-1], gateCollector)

			return facss, varEnd
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
				leftFactors, variableAtLeftEnd = currentCircuit.compile(left, gateCollector)
				rightFactors, variableAtRightEnd = currentCircuit.compile(right, gateCollector)
				break
			case "+":
				leftFactors, variableAtLeftEnd = currentCircuit.compile(left, gateCollector)
				rightFactors, variableAtRightEnd = currentCircuit.compile(right, gateCollector)
				return addFactors(leftFactors, rightFactors), variableAtLeftEnd || variableAtRightEnd
			case "/":
				leftFactors, variableAtLeftEnd = currentCircuit.compile(left, gateCollector)
				rightFactors, variableAtRightEnd = currentCircuit.compile(right, gateCollector)
				rightFactors = invertFactors(rightFactors)
				break
			case "-":
				leftFactors, variableAtLeftEnd = currentCircuit.compile(left, gateCollector)
				rightFactors, variableAtRightEnd = currentCircuit.compile(right, gateCollector)
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

		if out, ex := gateCollector.contains(sig.identifier); ex {
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
			value:    MultiplicationGateSignature{identifier: nTok, commonExtracted: sig.commonExtracted},
			leftIns:  newLef,
			rightIns: newRigh,
			output:   big.NewInt(int64(1)),
		}

		gateCollector.Add(rootGate)

		return factors{{typ: nTok, multiplicative: sig.commonExtracted}}, true
	}

	panic(currentConstraint)
}

// GenerateR1CS generates the ER1CS polynomials from the Circuit
func (p *Program) GatesToR1CS(mGates []*Gate) (r1CS *ER1CS) {
	// from flat code to ER1CS
	r1CS = &ER1CS{}
	neutralElement := "1"

	//offset := len(p.GlobalInputs) + 2
	//  one + in1 +in2+... + gate1 + gate2 .. + randIn + randOut
	//size := offset + len(mGates)
	indexMap := make(map[string]int)
	r1CS.indexMap = indexMap
	indexMap[neutralElement] = len(indexMap)
	for _, v := range p.GlobalInputs {
		indexMap[v] = len(indexMap)
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

// GenerateR1CS generates the ER1CS polynomials from the Circuit
func (p *Program) GatesToSparseR1CS(mGates []*Gate) (r1CS *ER1CSSparse) {
	// from flat code to ER1CS
	r1CS = &ER1CSSparse{}
	neutralElement := "1"

	//offset := len(p.GlobalInputs) + 2
	//  one + in1 +in2+... + gate1 + gate2 .. + randIn + randOut
	//size := offset + len(mGates)
	indexMap := make(map[string]int)
	r1CS.indexMap = indexMap
	indexMap[neutralElement] = len(indexMap)
	for _, v := range p.GlobalInputs {
		indexMap[v] = len(indexMap)
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

	insertValue := func(val *factor, arr *utils.AvlTree) {
		if val.typ.Type != NumberToken {
			if _, ex := indexMap[val.typ.Identifier]; !ex {
				panic(fmt.Sprintf("%v index not found!!!", val))
			}
		}
		value := val.multiplicative
		//not that index is 0 if its a constant, since 0 is the map default if no entry was found
		arr.Insert(uint(indexMap[val.typ.Identifier]), value)
	}

	for _, g := range mGates {

		switch g.gateType {
		case multiplicationGate:
			aConstraint := utils.NewAvlTree()
			bConstraint := utils.NewAvlTree()
			eConstraint := utils.NewAvlTree()
			cConstraint := utils.NewAvlTree()

			for _, val := range g.leftIns {
				insertValue(val, aConstraint)
			}

			for _, val := range g.rightIns {
				insertValue(val, bConstraint)
			}
			cConstraint.Insert(uint(indexMap[g.value.identifier.Identifier]), g.output)

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
			aConstraint := utils.NewAvlTree()
			bConstraint := utils.NewAvlTree()
			eConstraint := utils.NewAvlTree()
			cConstraint := utils.NewAvlTree()

			for _, val := range g.expoIns {
				insertValue(val, eConstraint)
			}

			cConstraint.Insert(uint(indexMap[g.value.identifier.Identifier]), big.NewInt(int64(1)))

			r1CS.L = append(r1CS.L, aConstraint)
			r1CS.R = append(r1CS.R, bConstraint)
			r1CS.E = append(r1CS.E, eConstraint)
			r1CS.O = append(r1CS.O, cConstraint)
			break
		case equalityGate:
			aConstraint := utils.NewAvlTree()
			bConstraint := utils.NewAvlTree()
			eConstraint := utils.NewAvlTree()
			cConstraint := utils.NewAvlTree()

			for _, val := range g.leftIns {
				insertValue(val, aConstraint)
			}

			for _, val := range g.rightIns {
				insertValue(val, cConstraint)
			}

			bConstraint.Insert(uint(0), big.NewInt(int64(1)))

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
	aConstraint := utils.NewAvlTree()
	bConstraint := utils.NewAvlTree()
	eConstraint := utils.NewAvlTree()
	cConstraint := utils.NewAvlTree()

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
