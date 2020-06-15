package circuitcompiler

import (
	"fmt"
	"github.com/mottla/go-AlgebraicProgram-SNARK/utils"
	"math/big"
)

type gateContainer struct {
	orderedmGates    []*Gate
	computedFactors  map[string]bool
	splittedElements map[string][]string
}

func newGateContainer() *gateContainer {
	return &gateContainer{
		orderedmGates:    []*Gate{},
		computedFactors:  make(map[string]bool),
		splittedElements: map[string][]string{}, //the array stores the indices of the zeroOrOne check gates
	}
}

func (g *gateContainer) completeFunction(f factors) {

	//if len f is 1, we can simpl
	if f == nil || len(f) == 0 {
		return
	}
	//if the function {..return x*1} , we dont introduce a new gate, as knowledge proof of a multiplication with 1 is trivial and not necessary
	if len(f) == 1 && f[0].multiplicative.Cmp(bigOne) == 0 {
		return
	}
	//the function returned but had a extracted constant
	// example
	//main (x,y){
	//var x = y*y*3
	//return 4*x }
	// x will be set as y*y, and the 3 will be stored aside. each time we access x, we include the 3
	// if we now return, we get the factor 12. we expect the prover to perform the computation x*12
	// Note that some optimization still could be done here. if a gate is not used by others, we could multiply the factor into it
	// insteead of creating a new addition gate
	rootGate := &Gate{
		gateType:   additionGate,
		identifier: f.factorSignature(),
		leftIns:    f,
		outIns: factors{&factor{
			typ: Token{
				Type:       ARGUMENT,
				Identifier: f.factorSignature(),
			},
			multiplicative: bigOne,
		}},
	}
	g.Add(rootGate)

}

func (g *gateContainer) contains(tok string) bool {
	_, ex := g.computedFactors[tok]
	return ex
}

func (g *gateContainer) Add(gate *Gate) {

	//we want to reduce the number of exponentiations in the slower group G2
	//since a*b = b*a, we swap in case
	//if len(gate.rightIns) > len(gate.leftIns) {
	//	tmp := gate.rightIns
	//	gate.rightIns = gate.leftIns
	//	gate.leftIns = tmp
	//}

	if _, ex := g.computedFactors[gate.ID()]; !ex {
		g.computedFactors[gate.ID()] = true
		g.orderedmGates = append(g.orderedmGates, gate)
	}

	return
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
}

func newProgram() (program *Program) {
	program = &Program{
		globalFunction: newCircuit("global", nil),
		GlobalInputs:   []string{"1"},
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
	//we add the neutral element here
	concrete = append([]*big.Int{big.NewInt(1)}, concrete...)
	if len(abstract) != len(concrete) {
		panic("argument missmatch")
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

//Execute runs on a program and returns a precursor for the final R1CS description
func (p *Program) Execute() (orderedmGates []*Gate) {

	container := newGateContainer()
	mainCircuit := p.getMainCircuit()

	p.GlobalInputs = append(p.GlobalInputs, mainCircuit.Inputs...)

	for i := 0; i < mainCircuit.taskStack.len(); i++ {
		f, _, returns := mainCircuit.compile(mainCircuit.taskStack.data[i], container)
		container.completeFunction(f)
		if returns {
			break
		}
	}
	return container.orderedmGates
}

func (currentCircuit *function) rereferenceFunctionInputs(newInputs []*function) (oldInputs []*function) {
	if len(currentCircuit.Inputs) != len(newInputs) {
		panic("argument size missmatch")
	}
	for i, name := range currentCircuit.Inputs {
		oldInputs = append(oldInputs, currentCircuit.functions[name])
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
		} else if _, ex := currentCircuit.findFunctionInBloodline(currentConstraint.Output.Identifier); ex {
			return nil, false, false
		} else {
			panic(fmt.Sprintf("variable %s not declared", currentConstraint.Output.Identifier))
		}
	case IF:
		if len(currentConstraint.Inputs) == 0 || currentCircuit.checkStaticCondition(currentConstraint.Inputs[0]) {
			return currentCircuit.compile(&Constraint{
				Output: Token{
					Type:       FUNCTION_CALL,
					Identifier: currentConstraint.Output.Identifier,
				},
			}, gateCollector)
		} else {
			return nil, false, false
		}
	case FOR:
		for currentCircuit.checkStaticCondition(currentConstraint.Inputs[0]) {
			content := &Constraint{
				Output: Token{
					Type:       FUNCTION_CALL,
					Identifier: currentConstraint.Output.Identifier,
				},
			}
			f, v, retu := currentCircuit.compile(content, gateCollector)
			if retu {
				return f, v, true
			}
			currentCircuit.compile(currentConstraint.Inputs[1], gateCollector)
		}
		return nil, false, false
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
		default:

		}
	case ARGUMENT:
		fac := &factor{typ: Token{
			Type:       ARGUMENT,
			Identifier: currentConstraint.Output.Identifier,
		}, multiplicative: big.NewInt(1)}
		return factors{fac}, true, false
	case VARIABLE_OVERLOAD:

		if len(currentConstraint.Inputs) != 2 {
			panic("unexpected reach")
		}

		var toOverloadIdentifier = currentConstraint.Inputs[0].Output.Identifier
		if currentConstraint.Inputs[0].Output.Type == ARRAY_CALL {
			array := currentConstraint.Inputs[0]
			if len(array.Inputs) != 1 {
				panic("accessing array index failed")
			}
			//ar[?]
			indexFactors, variable, _ := currentCircuit.compile(array.Inputs[0], gateCollector)
			if variable {
				panic("cannot access array dynamically in an arithmetic circuit currently")
			}
			if len(facs) > 1 {
				panic("unexpected")
			}
			toOverloadIdentifier = fmt.Sprintf("%s[%v]", array.Output.Identifier, indexFactors[0].multiplicative.String())
		}
		context, ex := currentCircuit.getCircuitContainingConstraintInBloodline(toOverloadIdentifier)
		if !ex {
			panic("unexpected reach")
		}

		if cn, ex := currentCircuit.findFunctionInBloodline(currentConstraint.Inputs[1].Output.Identifier); ex && currentConstraint.Inputs[1].Output.Type != FUNCTION_CALL {
			context.functions[toOverloadIdentifier] = cn
			return nil, false, false
		}

		//TODO
		f2, _, _ := currentCircuit.compile(currentConstraint.Inputs[1], gateCollector)

		if f2.Len() != 1 {
			panic("later dude")
		}

		if ex {
			context.functions[toOverloadIdentifier] = f2[0].primitiveReturnfunction()
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
		case "SPLIT":
			if len(currentConstraint.Inputs) != 1 {
				panic("split")
			}

			//prepare input number Z
			arg := currentConstraint.Inputs[0].clone()
			in, _, _ := currentCircuit.compile(arg, gateCollector)
			if len(in) != 1 {
				panic("arguments in split must be pure")
			}

			//hmm what is this actually good for
			//sig := hashFactorsToBig(in).String()[:16]

			//get the number N of bits needed to represent an arbitrary element of the finite field
			N := utils.Field.ArithmeticField.Q.BitLen()
			//we create N new R1CS elements Z_i. 			//
			//each represents a bit of Z
			//each Z_i is introduced by a constraint  (Z_i - 1 ) * Z_i = 0, to ensure its either 0 or 1
			// Z_0 is the lsb
			sum := make([]*factor, N)

			for i := 0; i < N; i++ {
				nTok := Token{
					Type: ARGUMENT,
					//wirst the number, then the variable, to avoid collisions
					Identifier: fmt.Sprintf("%v%v", i, in[0].typ.Identifier),
				}
				zeroOrOneGate := &Gate{
					gateType:                zeroOrOneGate,
					identifier:              nTok.Identifier,
					arithmeticRepresentatnt: in[0].typ,
				}
				gateCollector.Add(zeroOrOneGate)

				sum[i] = &factor{
					typ:            nTok,
					multiplicative: new(big.Int).Lsh(bigOne, uint(i)),
				}
				// we need to add the bits during precompilations so we can access them like from an array
				//	currentCircuit.constraintMap
			}
			//add the sum constraint \sum Z_i 2^i = Z to ensure that the Zi are the bit representation of Z

			sumgate := &Gate{
				gateType:                sumCheckGate,
				arithmeticRepresentatnt: in[0].typ,
				leftIns:                 sum,
				noNewOutput:             true,
			}
			//cConstraint[indexMap[g.value.identifier.Identifier]] = g.extractedConstants
			gateCollector.Add(sumgate)
			return nil, false, false
		case "AND":
			if len(currentConstraint.Inputs) != 2 {
				panic("addition constraint requires 2 arguments")
			}
			//leftClone := currentConstraint.Inputs[0].clone()
			//rightClone := currentConstraint.Inputs[1].clone()
			//leftFactors, _, _ := currentCircuit.compile(leftClone, gateCollector)
			//rightFactors, _, _ := currentCircuit.compile(rightClone, gateCollector)
		case "NAND":
		case "OR":
		case "NOT":
		case "addGateConstraint":
			if len(currentConstraint.Inputs) != 2 {
				panic("addition constraint requires 2 arguments")
			}
			leftClone := currentConstraint.Inputs[0].clone()
			rightClone := currentConstraint.Inputs[1].clone()
			leftFactors, _, _ := currentCircuit.compile(leftClone, gateCollector)
			rightFactors, _, _ := currentCircuit.compile(rightClone, gateCollector)
			commonExtracted, extractedLeft, extractedRight := extractConstant(leftFactors, rightFactors)

			rootGate := &Gate{
				gateType: additionGate,
				leftIns:  addFactors(extractedLeft, extractedRight),
			}

			nTok := Token{
				Type:       ARGUMENT,
				Identifier: rootGate.setAndGetID(),
			}
			gateCollector.Add(rootGate)
			rootGate.outIns = factors{&factor{
				typ:            nTok,
				multiplicative: bigOne,
			}}
			return factors{&factor{
				typ:            nTok,
				multiplicative: commonExtracted,
			}}, true, false
		case "scalarBaseMultiply":
			if len(currentConstraint.Inputs) != 1 {
				panic("scalarBaseMultiply argument missmatch")
			}
			exponentInputFactors, _, _ := currentCircuit.compile(currentConstraint.Inputs[0], gateCollector)

			rootGate := &Gate{
				gateType: scalarBaseMultiplyGate,
				expoIns:  exponentInputFactors,
			}

			gateCollector.Add(rootGate)

			return factors{&factor{
				typ:            Token{Identifier: rootGate.ID(), Type: ARGUMENT},
				multiplicative: bigOne,
			}}, true, false
		case "equal":
			if len(currentConstraint.Inputs) != 2 {
				panic("equality constraint requires 2 arguments")
			}
			leftClone := currentConstraint.Inputs[0].clone()
			rightClone := currentConstraint.Inputs[1].clone()
			leftFactors, _, _ := currentCircuit.compile(leftClone, gateCollector)
			rightFactors, _, _ := currentCircuit.compile(rightClone, gateCollector)

			rootGate := &Gate{
				gateType:    equalityGate,
				leftIns:     leftFactors,
				rightIns:    rightFactors,
				noNewOutput: true,
			}
			gateCollector.Add(rootGate)
			return nil, false, false
		default:
			var nextCircuit *function
			var ex bool
			if nextCircuit, ex = currentCircuit.findFunctionInBloodline(currentConstraint.Output.Identifier); !ex {
				panic(fmt.Sprintf("function %s not declared", currentConstraint.Output.Identifier))
			}
			//nextCircuit = nextCircuit.clone()
			inputs := make([]*function, len(currentConstraint.Inputs))
			//if the argument is a function call, we need to call it and give the result as argument i thinl
			//if the argument is a function, but not a call, we pass it on
			for i, v := range currentConstraint.Inputs {

				//TODO the order may matter.. check that.. the code here is troublesome I feel
				if cn, ex := currentCircuit.findFunctionInBloodline(v.Output.Identifier); ex && v.Output.Type != FUNCTION_CALL {
					inputs[i] = cn
					continue
				}

				f, varEnd, _ := currentCircuit.compile(v, gateCollector)

				if !varEnd {
					inputs[i] = f[0].primitiveReturnfunction()
					continue
				}

				//if i add them as functions, then they later can be replaced by functions.
				rmp := newCircuit(v.Output.Identifier, currentCircuit)
				rmp.taskStack.add(&Constraint{
					Output: Token{
						Type:       RETURN,
						Identifier: "",
					},
					Inputs: []*Constraint{v},
				})
				inputs[i] = rmp

			}
			//nextCircuit = nextCircuit.clone()
			old := nextCircuit.rereferenceFunctionInputs(inputs)

			for i := 0; i < nextCircuit.taskStack.len(); i++ {
				f, varend, returns := nextCircuit.compile(nextCircuit.taskStack.data[i], gateCollector)
				if returns {
					//gateCollector.appendFactors(f)
					nextCircuit.rereferenceFunctionInputs(old)
					return f, varend, true
				}
				gateCollector.completeFunction(f)
			}
			nextCircuit.rereferenceFunctionInputs(old)
			return nil, false, false
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

				if !(variableAtLeftEnd && variableAtRightEnd) {
					return mulFactors(leftFactors, rightFactors), variableAtLeftEnd || variableAtRightEnd, currentConstraint.Output.Type == RETURN
				}
				commonFactor, newLeft, newRight := extractConstant(leftFactors, rightFactors)
				mGate := &Gate{
					gateType: multiplicationGate,
					leftIns:  newLeft,
					rightIns: newRight,
				}
				gateCollector.Add(mGate)

				nTok := Token{Type: ARGUMENT, Identifier: mGate.ID()}
				mGate.outIns = factors{&factor{
					typ:            nTok,
					multiplicative: bigOne,
				}}
				return factors{{typ: nTok, multiplicative: commonFactor}}, true, currentConstraint.Output.Type == RETURN
			case "+":
				leftFactors, variableAtLeftEnd, _ = currentCircuit.compile(left, gateCollector)
				rightFactors, variableAtRightEnd, _ = currentCircuit.compile(right, gateCollector)
				return addFactors(leftFactors, rightFactors), variableAtLeftEnd || variableAtRightEnd, currentConstraint.Output.Type == RETURN
			case "/":
				leftFactors, variableAtLeftEnd, _ = currentCircuit.compile(left, gateCollector)
				rightFactors, variableAtRightEnd, _ = currentCircuit.compile(right, gateCollector)

				if !variableAtRightEnd { // (x1+x2..)/6

					return mulFactors(leftFactors, invertFactors(rightFactors)), variableAtRightEnd || variableAtLeftEnd, currentConstraint.Output.Type == RETURN
				}

				gcdl, facL := factorSignature(leftFactors)
				gcdR, facR := factorSignature(rightFactors)
				commonF := field.Div(gcdl, gcdR)
				mGate := &Gate{
					gateType: multiplicationGate,
					rightIns: facR,
					outIns:   facL,
				}
				gateCollector.Add(mGate)
				nTok := Token{Type: ARGUMENT, Identifier: mGate.ID()}
				mGate.leftIns = factors{&factor{
					typ:            nTok,
					multiplicative: bigOne,
				}}
				return factors{{typ: nTok, multiplicative: commonF}}, true, currentConstraint.Output.Type == RETURN

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

	}
	panic(currentConstraint)
}

// GenerateR1CS generates the ER1CS Language from an array of gates
func (p *Program) GatesToR1CS(mGates []*Gate, randomize bool) (r1CS *ER1CS) {
	// from flat code to ER1CS
	r1CS = &ER1CS{}
	r1CS.splitmap = make(map[string][]uint)

	//offset := len(p.GlobalInputs) + 2
	//  one + in1 +in2+... + gate1 + gate2 .. + randIn + randOut
	//size := offset + len(mGates)
	indexMap := make(map[string]uint)
	r1CS.indexMap = indexMap

	for _, v := range p.GlobalInputs {
		indexMap[v] = uint(len(indexMap))
	}

	for _, v := range mGates {
		//there are gates, which do not increase the size of the trace such as equality check constraint, sum check constraint after binary split
		if v.noNewOutput {
			//size = size - 1
			continue
		}
		if _, ex := indexMap[v.identifier]; !ex {
			indexMap[v.identifier] = uint(len(indexMap))

		} else {
			panic(fmt.Sprintf("rewriting %v ", v.identifier))
		}
		//we store where a variables bit representatives are
		if v.gateType == zeroOrOneGate {
			if _, ex := r1CS.splitmap[v.arithmeticRepresentatnt.Identifier]; !ex {
				r1CS.splitmap[v.arithmeticRepresentatnt.Identifier] = []uint{indexMap[v.identifier]}
			} else {
				r1CS.splitmap[v.arithmeticRepresentatnt.Identifier] = append(r1CS.splitmap[v.arithmeticRepresentatnt.Identifier], indexMap[v.identifier])
			}
		}
	}

	if randomize {
		indexMap[randInput] = uint(len(indexMap))
		indexMap[randOutput] = uint(len(indexMap))
	}

	insertValue := func(val *factor, arr []*big.Int) {
		if val.typ.Type != NumberToken {
			if _, ex := indexMap[val.typ.Identifier]; !ex {
				panic(fmt.Sprintf("%v index not found!!!", val))
			}
		}
		value := val.multiplicative
		//not that index is 0 if its a constant, since 0 is the map default if no entry was found
		arr[indexMap[val.typ.Identifier]] = utils.Field.ArithmeticField.Add(arr[indexMap[val.typ.Identifier]], value)
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

			for _, val := range g.outIns {
				insertValue(val, cConstraint)
			}

			//cConstraint[indexMap[g.identifier]] = g.extractedConstants

			//cConstraint[indexMap[g.value.identifier]] = big.NewInt(int64(1))

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

			cConstraint[indexMap[g.identifier]] = big.NewInt(int64(1))

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
		case zeroOrOneGate:
			// (n-1)n = 0 to ensure n == 1 or 0
			aConstraint := utils.ArrayOfBigZeros(size)
			bConstraint := utils.ArrayOfBigZeros(size)
			eConstraint := utils.ArrayOfBigZeros(size)
			cConstraint := utils.ArrayOfBigZeros(size)

			aConstraint[0] = big.NewInt(int64(-1))
			aConstraint[indexMap[g.identifier]] = big.NewInt(int64(1))
			bConstraint[indexMap[g.identifier]] = big.NewInt(int64(1))
			r1CS.L = append(r1CS.L, aConstraint)
			r1CS.R = append(r1CS.R, bConstraint)
			r1CS.E = append(r1CS.E, eConstraint)
			r1CS.O = append(r1CS.O, cConstraint)
			break
		case additionGate:
			aConstraint := utils.ArrayOfBigZeros(size)
			bConstraint := utils.ArrayOfBigZeros(size)
			eConstraint := utils.ArrayOfBigZeros(size)
			cConstraint := utils.ArrayOfBigZeros(size)

			for _, val := range g.leftIns {
				insertValue(val, aConstraint)
			}
			bConstraint[0] = big.NewInt(int64(1))
			for _, val := range g.outIns {
				insertValue(val, cConstraint)
			}
			r1CS.L = append(r1CS.L, aConstraint)
			r1CS.R = append(r1CS.R, bConstraint)
			r1CS.E = append(r1CS.E, eConstraint)
			r1CS.O = append(r1CS.O, cConstraint)
			break
		case sumCheckGate:
			aConstraint := utils.ArrayOfBigZeros(size)
			bConstraint := utils.ArrayOfBigZeros(size)
			eConstraint := utils.ArrayOfBigZeros(size)
			cConstraint := utils.ArrayOfBigZeros(size)

			for _, val := range g.leftIns {
				insertValue(val, aConstraint)
			}
			bConstraint[0] = big.NewInt(int64(1))
			cConstraint[indexMap[g.arithmeticRepresentatnt.Identifier]] = big.NewInt(int64(1))
			r1CS.L = append(r1CS.L, aConstraint)
			r1CS.R = append(r1CS.R, bConstraint)
			r1CS.E = append(r1CS.E, eConstraint)
			r1CS.O = append(r1CS.O, cConstraint)
			break
		default:
			panic("no supported gate type")
		}
	}

	if randomize {
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

	}

	return
}

// GenerateR1CS generates the ER1CS polynomials from the function
func (p *Program) GatesToSparseR1CS(mGates []*Gate, randomize bool) (r1CS *ER1CSSparse) {
	// from flat code to ER1CS
	r1CS = &ER1CSSparse{}
	r1CS.splitmap = make(map[string][]uint)
	//offset := len(p.GlobalInputs) + 2
	//  one + in1 +in2+... + gate1 + gate2 .. + randIn + randOut
	//size := offset + len(mGates)
	indexMap := make(map[string]uint)
	r1CS.indexMap = indexMap

	for _, v := range p.GlobalInputs {
		indexMap[v] = uint(len(indexMap))
	}

	for _, v := range mGates {
		if v.noNewOutput {
			//size = size - 1
			continue
		}
		if _, ex := indexMap[v.ID()]; !ex {
			indexMap[v.ID()] = uint(len(indexMap))
		} else {
			panic(fmt.Sprintf("rewriting %v ", v.identifier))
		}

		////we store where a variables bit representatives are
		if v.gateType == zeroOrOneGate {
			if _, ex := r1CS.splitmap[v.arithmeticRepresentatnt.Identifier]; !ex {
				r1CS.splitmap[v.arithmeticRepresentatnt.Identifier] = []uint{(indexMap[v.identifier])}
			} else {
				r1CS.splitmap[v.arithmeticRepresentatnt.Identifier] = append(r1CS.splitmap[v.arithmeticRepresentatnt.Identifier], (indexMap[v.identifier]))
			}
		}
	}
	if randomize {
		indexMap[randInput] = uint(len(indexMap))
		indexMap[randOutput] = uint(len(indexMap))
	}

	insertValue := func(val *factor, arr *utils.AvlTree) {
		if val.typ.Type != NumberToken {
			if _, ex := indexMap[val.typ.Identifier]; !ex {
				panic(fmt.Sprintf("%v index not found!!!", val))
			}
		}
		value := val.multiplicative
		//not that index is 0 if its a constant, since 0 is the map default if no entry was found
		arr.Put(uint(indexMap[val.typ.Identifier]), value, utils.Field.ArithmeticField.Add)
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

			for _, val := range g.outIns {
				insertValue(val, cConstraint)
			}

			r1CS.L = append(r1CS.L, aConstraint)
			r1CS.R = append(r1CS.R, bConstraint)
			r1CS.E = append(r1CS.E, eConstraint)
			r1CS.O = append(r1CS.O, cConstraint)
			break
		case additionGate:
			aConstraint := utils.NewAvlTree()
			bConstraint := utils.NewAvlTree()
			eConstraint := utils.NewAvlTree()
			cConstraint := utils.NewAvlTree()

			for _, val := range g.leftIns {
				insertValue(val, aConstraint)
			}
			bConstraint.Insert(uint(0), big.NewInt(int64(1)))

			for _, val := range g.outIns {
				insertValue(val, cConstraint)
			}

			r1CS.L = append(r1CS.L, aConstraint)
			r1CS.R = append(r1CS.R, bConstraint)
			r1CS.E = append(r1CS.E, eConstraint)
			r1CS.O = append(r1CS.O, cConstraint)
			break
		case sumCheckGate:
			aConstraint := utils.NewAvlTree()
			bConstraint := utils.NewAvlTree()
			eConstraint := utils.NewAvlTree()
			cConstraint := utils.NewAvlTree()

			for _, val := range g.leftIns {
				insertValue(val, aConstraint)
			}
			bConstraint.Insert(uint(0), big.NewInt(int64(1)))

			cConstraint.Insert(indexMap[g.arithmeticRepresentatnt.Identifier], big.NewInt(int64(1)))

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

			cConstraint.Insert(uint(indexMap[g.identifier]), big.NewInt(int64(1)))

			r1CS.L = append(r1CS.L, aConstraint)
			r1CS.R = append(r1CS.R, bConstraint)
			r1CS.E = append(r1CS.E, eConstraint)
			r1CS.O = append(r1CS.O, cConstraint)
			break
		case zeroOrOneGate:
			// (n-1)n = 0 to ensure n == 1 or 0
			aConstraint := utils.NewAvlTree()
			bConstraint := utils.NewAvlTree()
			eConstraint := utils.NewAvlTree()
			cConstraint := utils.NewAvlTree()

			aConstraint.Insert(0, big.NewInt(int64(-1)))
			aConstraint.Insert(indexMap[g.identifier], big.NewInt(int64(1)))
			bConstraint.Insert(indexMap[g.identifier], big.NewInt(int64(1)))
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
	if randomize {
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
	}
	r1CS.NumberOfGates = len(mGates)
	r1CS.WitnessLength = len(indexMap)
	return
}
