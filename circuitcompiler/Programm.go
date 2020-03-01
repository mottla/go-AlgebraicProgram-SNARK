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
	if f == nil {
		return
	}
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
	globalFunction *function
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
func (p *Program) getMainCircuit() *function {
	return p.globalFunction.functions["main"]
}

func (p *Program) ReduceCombinedTree() (orderedmGates []*Gate) {

	container := newGateContainer()
	mainCircuit := p.getMainCircuit()

	for _, v := range mainCircuit.Inputs {
		mainCircuit.constraintMap[v].Output.Type = ARGUMENT
	}

	p.GlobalInputs = mainCircuit.Inputs
	p.computedFactors = make(map[Token]MultiplicationGateSignature)

	for i := 0; i < mainCircuit.taskStack.len(); i++ {
		f, _, returns := mainCircuit.compile(mainCircuit.taskStack.data[i], container)
		container.appendFactors(f)
		if returns {
			break
		}

	}
	return container.orderedmGates
}

func (currentCircuit *function) rereferenceFunctionInputs(newInputs []*function) {
	if len(currentCircuit.Inputs) != len(newInputs) {
		panic("argument size missmatch")
	}
	for i, name := range currentCircuit.Inputs {
		currentCircuit.functions[name] = newInputs[i]
	}
	return

}

//recursively walks through the parse tree to create a list of all
//multiplication gates needed for the QAP construction
//Takes into account, that multiplication with constants and addition (= substraction) can be reduced, and does so
func (currentCircuit *function) compile(currentConstraint *Constraint, gateCollector *gateContainer) (facs factors, variableEnd bool, reachedReturn bool) {

	switch currentConstraint.Output.Type {
	case NumberToken:
		value, success := utils.Field.ArithmeticField.StringToFieldElement(currentConstraint.Output.Identifier)
		if !success {
			panic("not a constant")
		}
		return factors{{typ: Token{Type: NumberToken, Identifier: currentConstraint.Output.Identifier}, multiplicative: value}}, false, false
	case IDENTIFIER_VARIABLE:
		// an identifier is always a lone indentifier. If such one is reached. we are at a leaf and either can resolve him as argument or declared function/variable
		if con, ex := currentCircuit.findConstraintInBloodline(currentConstraint.Output.Identifier); ex {
			return currentCircuit.compile(con, gateCollector)
		} else {
			panic(fmt.Sprintf("variable %s not declared", currentConstraint.Output.Identifier))
		}

	case IDENTIFIER_FUNCTION:
		//if con, ex := currentCircuit.findFunctionInBloodline(currentConstraint.Output.Identifier); ex {
		//
		//	return con.compile(con.taskStack.data[0], gateCollector)
		//}
		fac := &factor{typ: Token{
			Type:       FUNCTION_CALL,
			Identifier: currentConstraint.Output.Identifier, //+string(hashTraceBuildup),
		}, multiplicative: big.NewInt(1)}
		return factors{fac}, true, false
		panic("sdaf")
	case IF:
		if currentCircuit.checkStaticCondition(currentConstraint.Inputs[0]) {
			return currentCircuit.compile(&Constraint{
				Output: Token{
					Type:       FUNCTION_CALL,
					Identifier: currentConstraint.Output.Identifier,
				},
			}, gateCollector)
		} else {
			return nil, false, false
		}
		//currentCircuit[currentConstraint.]
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
			return factors{fac}, false, true
		case 1:
			f, v, _ := currentCircuit.compile(currentConstraint.Inputs[0], gateCollector)
			return f, v, true
		case 3:
		default:
			panic(currentConstraint)
		}
	case ARGUMENT:
		fac := &factor{typ: Token{
			Type:       ARGUMENT,
			Identifier: currentConstraint.Output.Identifier, //+string(hashTraceBuildup),
		}, multiplicative: big.NewInt(1)}
		return factors{fac}, true, false
	case VARIABLE_DECLARE:
		panic("unexpected reach")
	case VARIABLE_OVERLOAD:

		if len(currentConstraint.Inputs) != 1 {
			panic("unexpected reach")
		}
		f, _, _ := currentCircuit.compile(currentConstraint.Inputs[0], gateCollector)

		if f.Len() != 1 {
			panic("later dude")
		}
		rmp := newCircuit("asdf", nil)
		rmp.taskStack.add(&Constraint{
			Output: Token{
				Type:       RETURN,
				Identifier: "",
			},
			Inputs: []*Constraint{&Constraint{
				Output: f[0].typ,
			}},
		})

		if context, ex := currentCircuit.getCircuitContainingConstraintInBloodline(currentConstraint.Output.Identifier); ex {
			context.functions[currentConstraint.Output.Identifier] = rmp
		} else {
			panic("unexpected reach")
		}
		return nil, false, false

	case ARRAY_CALL:

		if len(currentConstraint.Inputs) != 1 {
			panic("accessing array index failed")
		}
		indexFactors, variable, _ := currentCircuit.compile(currentConstraint.Inputs[0], gateCollector)
		if variable {
			panic("cannot access array dynamically in an arithmetic circuit currently")
		}
		if len(facs) > 1 {
			panic("unexpected")
		}

		elementName := fmt.Sprintf("%s[%v]", currentConstraint.Output.Identifier, indexFactors[0].multiplicative.String())

		if con, ex := currentCircuit.findConstraintInBloodline(elementName); ex {
			return currentCircuit.compile(con, gateCollector)
		} else {
			panic(fmt.Sprintf("array %s not declared", currentConstraint.Output.Identifier))
		}

	case FUNCTION_CALL:
		switch currentConstraint.Output.Identifier {
		case "scalarBaseMultiply":
			if len(currentConstraint.Inputs) != 1 {
				panic("scalarBaseMultiply argument missmatch")
			}
			secretFactors, _, _ := currentCircuit.compile(currentConstraint.Inputs[0], gateCollector)

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
			}}, true, false
		case "equal":
			if len(currentConstraint.Inputs) != 2 {
				panic("equality constraint requires 2 arguments")
			}
			leftClone := currentConstraint.Inputs[0].clone()
			rightClone := currentConstraint.Inputs[1].clone()
			l, _, _ := currentCircuit.compile(leftClone, gateCollector)
			r, _, _ := currentCircuit.compile(rightClone, gateCollector)
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
			}}, true, false
			return
		default:
			var nextCircuit *function
			var ex bool
			if nextCircuit, ex = currentCircuit.findFunctionInBloodline(currentConstraint.Output.Identifier); !ex {
				panic(fmt.Sprintf("function %s not declared", currentConstraint.Output.Identifier))
			}

			inputs := make([]*function, len(currentConstraint.Inputs))
			//if the argument is a function call, we need to call it and give the result as argument i thinl
			//if the argument is a function, but not a call, we pass it on
			for i, v := range currentConstraint.Inputs {

				if cn, ex := currentCircuit.findFunctionInBloodline(v.Output.Identifier); ex && v.Output.Type != FUNCTION_CALL {
					inputs[i] = cn
					continue
				}
				f, _, _ := currentCircuit.compile(v, gateCollector)

				if f.Len() != 1 {
					panic("later dude")
				}
				rmp := newCircuit("asdf", nil)
				rmp.taskStack.add(&Constraint{
					Output: Token{
						Type:       RETURN,
						Identifier: "",
					},
					Inputs: []*Constraint{&Constraint{
						Output: f[0].typ,
					}},
				})
				inputs[i] = rmp
			}

			nextCircuit.rereferenceFunctionInputs(inputs)

			for i := 0; i < nextCircuit.taskStack.len(); i++ {
				f, varend, returns := nextCircuit.compile(nextCircuit.taskStack.data[i], gateCollector)
				if returns {
					//gateCollector.appendFactors(f)
					return f, varend, true
				}
				gateCollector.appendFactors(f)
			}
			return nil, false, false
			//panic("every function must return somewhere")
		}
	default:

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
				leftFactors, variableAtLeftEnd, _ = currentCircuit.compile(left, gateCollector)
				rightFactors, variableAtRightEnd, _ = currentCircuit.compile(right, gateCollector)
				break
			case "+":
				leftFactors, variableAtLeftEnd, _ = currentCircuit.compile(left, gateCollector)
				rightFactors, variableAtRightEnd, _ = currentCircuit.compile(right, gateCollector)
				return addFactors(leftFactors, rightFactors), variableAtLeftEnd || variableAtRightEnd, currentConstraint.Output.Type == RETURN
			case "/":
				leftFactors, variableAtLeftEnd, _ = currentCircuit.compile(left, gateCollector)
				rightFactors, variableAtRightEnd, _ = currentCircuit.compile(right, gateCollector)
				rightFactors = invertFactors(rightFactors)
				break
			case "-":
				leftFactors, variableAtLeftEnd, _ = currentCircuit.compile(left, gateCollector)
				rightFactors, variableAtRightEnd, _ = currentCircuit.compile(right, gateCollector)
				rightFactors = negateFactors(rightFactors)
				return addFactors(leftFactors, rightFactors), variableAtLeftEnd || variableAtRightEnd, currentConstraint.Output.Type == RETURN
			}
			break
		case AssignmentOperatorToken:
			break
		default:
			panic("unsupported operation")
		}

		if !(variableAtLeftEnd && variableAtRightEnd) {
			return mulFactors(leftFactors, rightFactors), variableAtLeftEnd || variableAtRightEnd, currentConstraint.Output.Type == RETURN
		}
		sig, newLef, newRigh := extractConstant(leftFactors, rightFactors)

		if out, ex := gateCollector.contains(sig.identifier); ex {
			return factors{{typ: out.identifier, multiplicative: sig.commonExtracted}}, true, currentConstraint.Output.Type == RETURN
		}
		//currentConstraint.Output.Identifier += "@"
		//currentConstraint.Output.Identifier += sig.identifier.Identifier
		nTok := Token{
			//Type: currentConstraint.Output.Type,
			Type: ARGUMENT,
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

		return factors{{typ: nTok, multiplicative: sig.commonExtracted}}, true, currentConstraint.Output.Type == RETURN
	}

	panic(currentConstraint)
}

// GenerateR1CS generates the ER1CS polynomials from the function
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

// GenerateR1CS generates the ER1CS polynomials from the function
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
