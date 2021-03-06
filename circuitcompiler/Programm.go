package circuitcompiler

import (
	"fmt"
	"github.com/mottla/go-AlgebraicProgram-SNARK/utils"
	"math/big"
	"strconv"
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
	if f == nil || len(f) == 0 || f.isSingleNumber() {
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
		outIns: factors{factor{
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

	if !g.contains(gate.ID()) {
		g.computedFactors[gate.ID()] = true
		g.orderedmGates = append(g.orderedmGates, gate)
	} else {
		//fmt.Println("saved reuse of "+gate.String())
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
	PublicInputs   []string
}

func newProgram() (program *Program) {
	program = &Program{
		globalFunction: newCircuit("global", nil),
		PublicInputs:   []string{"1"},
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

	if len(abstract) != len(concrete) {
		panic(fmt.Sprintf("argument missmatch, programm requires %v inputs, you provided %v", len(abstract), len(concrete)))
	}

	res = make([]InputArgument, len(abstract))

	for k, v := range abstract {
		res[k] = InputArgument{identifier: v, value: concrete[k]}
	}

	return res
}

//returns the cardinality of all public inputs (+ 1 for the "one" signal)
func (p *Program) GlobalInputCount() int {
	return len(p.PublicInputs)
}
func (p *Program) GetMainCircuit() *function {
	return p.globalFunction.functions["main"]
}

func (currentCircuit *function) getFunctionInputs() (oldInputs []*function) {
	for _, name := range currentCircuit.Inputs {
		oldInputs = append(oldInputs, currentCircuit.functions[name])
	}
	return

}
func (currentCircuit *function) setFunctionInputs(inputs []string, fktInputs []*function) {
	currentCircuit.Inputs = inputs
	for i, name := range inputs {
		currentCircuit.functions[name] = fktInputs[i]
	}
	return

}

func (currentCircuit *function) getsLoadedWith(newInputs []*function) (allArgumentsLoaded bool) {
	allArgumentsLoaded = len(currentCircuit.Inputs) == len(newInputs)
	if len(currentCircuit.Inputs) < len(newInputs) {
		panic(fmt.Sprintf("%v takes %v arguments, got %v", currentCircuit.Name, len(currentCircuit.Inputs), len(newInputs)))
	}
	for i := 0; i < len(newInputs); i++ {
		currentCircuit.functions[currentCircuit.Inputs[i]] = newInputs[i]
	}
	currentCircuit.Inputs = currentCircuit.Inputs[len(newInputs):]
	return
}

//helper function
func (currentCircuit *function) resolveArrayName(c *Constraint) string {
	var arrayIdentifier = c.Output.Identifier
	//if len(c.Inputs) < 1 {
	//	panic("accessing array index failed")
	//}
	for _, in := range c.Inputs {
		indexFactors, _, _ := currentCircuit.compile(in, newGateContainer())
		if !indexFactors.isSingleNumber() {
			panic("cannot access array dynamically in an arithmetic circuit currently")
		}
		if len(indexFactors) > 1 {
			panic("unexpected")
		}
		tmp, err := strconv.ParseInt(indexFactors[0].typ.Identifier, 10, 64)
		if err != nil || tmp < 0 {
			panic(err.Error())
		}
		arrayIdentifier += fmt.Sprintf("[%v]", tmp)
	}
	return arrayIdentifier
}

//Execute runs on a program and returns a precursor for the final R1CS description
func (p *Program) Execute() (orderedmGates []*Gate) {

	container := newGateContainer()
	mainCircuit := p.GetMainCircuit()

	for i := 0; i < mainCircuit.taskStack.len(); i++ {
		f, returns, _ := mainCircuit.compile(mainCircuit.taskStack.data[i], container)
		container.completeFunction(f)
		if returns {
			break
		}
	}
	return container.orderedmGates
}

func (currentCircuit *function) execute(gateCollector *gateContainer) (facs factors, returned bool, preloadedFunction function) {

	for _, task := range currentCircuit.taskStack.data {
		f, returs, fkt := currentCircuit.compile(task, gateCollector)
		if returs {
			return f, true, fkt
		}
		//gateCollector.completeFunction(f)
	}
	return nil, false, function{}
}

//recursively walks through the parse tree to create a list of all
//multiplication gates needed for the QAP construction
//Takes into account, that multiplication with constants and addition (= substraction) can be reduced, and does so
//
func (currentCircuit *function) compile(currentConstraint *Constraint, gateCollector *gateContainer) (facs factors, reachedReturn bool, preloadedFunction function) {

	switch currentConstraint.Output.Type {
	case NumberToken:
		value, success := utils.Field.ArithmeticField.StringToFieldElement(currentConstraint.Output.Identifier)
		if !success {
			panic("not a constant")
		}
		f := factor{typ: Token{Type: NumberToken, Identifier: currentConstraint.Output.Identifier}, multiplicative: value}
		return factors{f}, false, function{}
	case IDENTIFIER_VARIABLE:
		// an identifier is always a lone indentifier. If such one is reached. we are at a leaf and either can resolve him as argument or declared function/variable

		if f, ex := currentCircuit.findFunctionInBloodline(currentConstraint.Output.Identifier); ex {
			if f.isNumber {
				fac := factor{typ: Token{Type: NumberToken, Identifier: f.Name}, multiplicative: f.value}
				return factors{fac}, false, function{}
			}
			if len(f.Inputs) == 0 {

				if con, ex := currentCircuit.findConstraintInBloodline(currentConstraint.Output.Identifier); ex {
					return currentCircuit.compile(con, gateCollector)
				}
				panic(fmt.Sprintf("variable %s not declared", currentConstraint.Output.Identifier))
			}
			return nil, false, *f

			//return f.execute(gateCollector)

		}

		panic(fmt.Sprintf("variable %s not declared", currentConstraint.Output.Identifier))

	case FOR:
		//we check the condition each time we rerun the loop
		for currentCircuit.checkStaticCondition(currentConstraint.Inputs[0]) {
			content := &Constraint{
				Output: Token{
					Type:       FUNCTION_CALL,
					Identifier: currentConstraint.Output.Identifier,
				},
			}
			f, retu, fkt := currentCircuit.compile(content, gateCollector)
			if retu {
				return f, true, fkt
			}
			currentCircuit.compile(currentConstraint.Inputs[1], gateCollector)
		}
		return nil, false, function{}
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
			fac := factor{typ: Token{
				Type: NumberToken,
			}, multiplicative: big.NewInt(1)}
			return factors{fac}, true, function{}
		case 1:
			f, _, fkt := currentCircuit.compile(currentConstraint.Inputs[0], gateCollector)
			return f, true, fkt
		default:

		}
	case ARGUMENT:
		fac := factor{typ: Token{
			Type:       ARGUMENT,
			Identifier: currentConstraint.Output.Identifier,
		}, multiplicative: big.NewInt(1)}
		return factors{fac}, false, function{}
	case VARIABLE_OVERLOAD:

		if len(currentConstraint.Inputs) != 2 {
			panic("unexpected reach")
		}

		var toOverloadIdentifier = currentConstraint.Inputs[0].Output.Identifier

		if currentConstraint.Inputs[0].Output.Type == ARRAY_CALL {
			// myArray[7*3] = expression
			toOverloadIdentifier = currentCircuit.resolveArrayName(currentConstraint.Inputs[0])
			//myArray[21] = expression
		}

		//resolve the expression
		facs, _, fkt := currentCircuit.compile(currentConstraint.Inputs[1], gateCollector)
		context, ex := currentCircuit.getCircuitContainingFunctionInBloodline(toOverloadIdentifier)
		if !ex {
			panic("does not exist")
		}
		if facs == nil {
			context.functions[toOverloadIdentifier] = &fkt
			return nil, false, function{}
		}
		//overwrite

		context.functions[toOverloadIdentifier] = facs.primitiveReturnfunction()

		return facs, false, function{}

	case ARRAY_CALL:
		resolvedName := currentCircuit.resolveArrayName(currentConstraint)
		if con, ex := currentCircuit.findConstraintInBloodline(resolvedName); ex {
			a, _, fkt := currentCircuit.compile(con, gateCollector)
			return a, false, fkt
		} else {
			panic(fmt.Sprintf("array %s not declared", resolvedName))
		}
	case IF:
		if len(currentConstraint.Inputs) == 0 || currentCircuit.checkStaticCondition(currentConstraint.Inputs[0]) {
			return currentCircuit.compile(&Constraint{
				Output: Token{
					Type:       IF_FUNCTION_CALL,
					Identifier: currentConstraint.Output.Identifier,
				},
			}, gateCollector)
		} else {
			return nil, false, function{}
		}
	case IF_FUNCTION_CALL:
		var nextCircuit *function
		var ex bool
		if nextCircuit, ex = currentCircuit.findFunctionInBloodline(currentConstraint.Output.Identifier); !ex {
			panic(fmt.Sprintf("function %s not declared", currentConstraint.Output.Identifier))
		}
		return nextCircuit.execute(gateCollector)
	case FUNCTION_CALL:
		switch currentConstraint.Output.Identifier {
		case "BREAK":
			// DEBUG function. Set a break point somewhere and read all arguments that were passed to BREAK(args...)
			for _, v := range currentConstraint.Inputs {
				in, _, _ := currentCircuit.compile(v.clone(), gateCollector)

				st := fmt.Sprintf("%v , %v", v.String(), in)
				fmt.Println(st)
			}
			//break point
			return nil, false, function{}
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
			sum := make([]factor, N)

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

				sum[i] = factor{
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
			return nil, false, function{}
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
			rootGate.outIns = factors{factor{
				typ:            nTok,
				multiplicative: bigOne,
			}}
			fres := factor{
				typ:            nTok,
				multiplicative: commonExtracted,
			}
			return factors{fres}, false, function{}
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
			fres := factor{
				typ:            Token{Identifier: rootGate.ID(), Type: ARGUMENT},
				multiplicative: bigOne,
			}
			return factors{fres}, false, function{}
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
			return nil, false, function{}
		default:
			var nextCircuit *function
			var ex bool

			if nextCircuit, ex = currentCircuit.findFunctionInBloodline(currentConstraint.Output.Identifier); !ex {
				panic(fmt.Sprintf("function %s not declared", currentConstraint.Output.Identifier))
			}
			var nxt *function
			nxt = nextCircuit.flatCopy()

			inputs := make([]*function, len(currentConstraint.Inputs))
			//if the argument is a function call, we need to call it and give the result as argument i thinl
			//if the argument is a function, but not a call, we pass it on
			for i, v := range currentConstraint.Inputs {

				fkts, _, retFkt := currentCircuit.compile(v, gateCollector)
				if fkts == nil {
					inputs[i] = &retFkt
					continue
				}
				inputs[i] = fkts.primitiveReturnfunction()
			}

			//old := nxt.getFunctionInputs()
			//old2 := nxt.Inputs
			//defer nxt.setFunctionInputs(old2,old)
			isReadyToEvaluate := nxt.getsLoadedWith(inputs)
			if !isReadyToEvaluate {
				return nil, false, *nxt
			}
			facs, _, fkt := nxt.execute(gateCollector)
			return facs, false, fkt
		}
	default:
	}

	if len(currentConstraint.Inputs) == 3 {

		left := currentConstraint.Inputs[1]
		right := currentConstraint.Inputs[2]
		operation := currentConstraint.Inputs[0].Output

		var leftFactors, rightFactors factors

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
				leftFactors, _, _ = currentCircuit.compile(left, gateCollector)
				rightFactors, _, _ = currentCircuit.compile(right, gateCollector)

				if leftFactors.isSingleNumber() || rightFactors.isSingleNumber() {
					return mulFactors(leftFactors, rightFactors), currentConstraint.Output.Type == RETURN, function{}
				}
				commonFactor, newLeft, newRight := extractConstant(leftFactors, rightFactors)
				mGate := &Gate{
					gateType: multiplicationGate,
					leftIns:  newLeft,
					rightIns: newRight,
				}
				gateCollector.Add(mGate)

				nTok := Token{Type: ARGUMENT, Identifier: mGate.ID()}
				mGate.outIns = factors{factor{
					typ:            nTok,
					multiplicative: bigOne,
				}}
				f := factor{typ: nTok, multiplicative: commonFactor}
				return factors{f}, currentConstraint.Output.Type == RETURN, function{}
			case "/":
				leftFactors, _, _ = currentCircuit.compile(left, gateCollector)
				rightFactors, _, _ = currentCircuit.compile(right, gateCollector)

				if rightFactors.isSingleNumber() { // (x1+x2..)/6
					return mulFactors(leftFactors, invertFactors(rightFactors)), currentConstraint.Output.Type == RETURN, function{}
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
				mGate.leftIns = factors{factor{
					typ:            nTok,
					multiplicative: bigOne,
				}}
				f := factor{typ: nTok, multiplicative: commonF}
				return factors{f}, currentConstraint.Output.Type == RETURN, function{}
			case "+":
				leftFactors, _, _ = currentCircuit.compile(left, gateCollector)
				rightFactors, _, _ = currentCircuit.compile(right, gateCollector)
				addedFactors := addFactors(leftFactors, rightFactors)
				return addedFactors, currentConstraint.Output.Type == RETURN, function{}

			case "-":
				leftFactors, _, _ = currentCircuit.compile(left, gateCollector)
				rightFactors, _, _ = currentCircuit.compile(right, gateCollector)
				rightFactors = negateFactors(rightFactors)
				addedFactors := addFactors(leftFactors, rightFactors)
				return addedFactors, currentConstraint.Output.Type == RETURN, function{}
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
	r1CS.splitmap = make(map[string][]int)

	//offset := len(p.PublicInputs) + 2
	//  one + in1 +in2+... + gate1 + gate2 .. + randIn + randOut
	//size := offset + len(mGates)
	indexMap := make(map[string]int)
	r1CS.indexMap = indexMap

	//first we add the public inputs
	for _, v := range p.PublicInputs {
		indexMap[v] = len(indexMap)
	}
	for _, v := range p.GetMainCircuit().Inputs {
		if _, ex := indexMap[v]; ex {
			continue
		}
		indexMap[v] = len(indexMap)
	}

	for _, v := range mGates {
		//there are gates, which do not increase the size of the trace such as equality check constraint, sum check constraint after binary split
		if v.noNewOutput {
			//size = size - 1
			continue
		}
		if _, ex := indexMap[v.identifier]; !ex {
			indexMap[v.identifier] = len(indexMap)

		} else {
			panic(fmt.Sprintf("rewriting %v ", v.identifier))
		}
		//we store where a variables bit representatives are
		if v.gateType == zeroOrOneGate {
			if _, ex := r1CS.splitmap[v.arithmeticRepresentatnt.Identifier]; !ex {
				r1CS.splitmap[v.arithmeticRepresentatnt.Identifier] = []int{indexMap[v.identifier]}
			} else {
				r1CS.splitmap[v.arithmeticRepresentatnt.Identifier] = append(r1CS.splitmap[v.arithmeticRepresentatnt.Identifier], indexMap[v.identifier])
			}
		}
	}

	if randomize {
		indexMap[randInput] = len(indexMap)
		indexMap[randOutput] = len(indexMap)
	}

	insertValue := func(val factor, arr []*big.Int) {
		if val.typ.Type == NumberToken {
			arr[0] = val.multiplicative
			return
		}
		index, ex := indexMap[val.typ.Identifier]
		if !ex {
			panic(fmt.Sprintf("%v index not found!!!", val))
		}
		arr[index] = val.multiplicative
		//arr[indexMap[val.typ.Identifier]] = utils.Field.ArithmeticField.Add(arr[indexMap[val.typ.Identifier]], value)
		fmt.Print("")
	}
	size := len(indexMap)
	for _, g := range mGates {
		//we want to reduce the number of exponentiations in the slower group G2
		//since a*b = b*a, we swap in case
		if len(g.rightIns) > len(g.leftIns) {
			tmp := g.rightIns
			g.rightIns = g.leftIns
			g.leftIns = tmp
		}

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

		insertValue(factor{typ: Token{Identifier: randInput}, multiplicative: bigOne}, aConstraint)
		insertValue(factor{typ: Token{Identifier: randInput}, multiplicative: bigOne}, bConstraint)
		insertValue(factor{typ: Token{Identifier: randInput}, multiplicative: bigOne}, eConstraint)
		insertValue(factor{typ: Token{Identifier: randOutput}, multiplicative: bigOne}, cConstraint)

		r1CS.L = append(r1CS.L, aConstraint)
		r1CS.R = append(r1CS.R, bConstraint)
		r1CS.E = append(r1CS.E, eConstraint)
		r1CS.O = append(r1CS.O, cConstraint)

	}
	r1CS.NumberOfGates = len(r1CS.L)
	r1CS.WitnessLength = len(indexMap)
	return
}

// GenerateR1CS generates the ER1CS polynomials from the function
func (p *Program) GatesToSparseR1CS(mGates []*Gate, randomize bool) (r1CS *ER1CSSparse) {
	// from flat code to ER1CS
	r1CS = &ER1CSSparse{}
	r1CS.splitmap = make(map[string][]int)
	//offset := len(p.PublicInputs) + 2
	//  one + in1 +in2+... + gate1 + gate2 .. + randIn + randOut
	//size := offset + len(mGates)
	indexMap := make(map[string]int)
	r1CS.indexMap = indexMap

	for _, v := range p.PublicInputs {
		indexMap[v] = len(indexMap)
	}
	for _, v := range p.GetMainCircuit().Inputs {
		if _, ex := indexMap[v]; ex {
			continue
		}
		indexMap[v] = len(indexMap)
	}

	for _, v := range mGates {
		if v.noNewOutput {
			//size = size - 1
			continue
		}
		if _, ex := indexMap[v.ID()]; !ex {
			indexMap[v.ID()] = len(indexMap)
		} else {
			panic(fmt.Sprintf("rewriting %v ", v.identifier))
		}

		////we store where a variables bit representatives are
		if v.gateType == zeroOrOneGate {
			if _, ex := r1CS.splitmap[v.arithmeticRepresentatnt.Identifier]; !ex {
				r1CS.splitmap[v.arithmeticRepresentatnt.Identifier] = []int{indexMap[v.identifier]}
			} else {
				r1CS.splitmap[v.arithmeticRepresentatnt.Identifier] = append(r1CS.splitmap[v.arithmeticRepresentatnt.Identifier], indexMap[v.identifier])
			}
		}
	}
	if randomize {
		indexMap[randInput] = len(indexMap)
		indexMap[randOutput] = len(indexMap)
	}

	insertValue := func(val factor, arr *utils.AvlTree) {
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
		//we want to reduce the number of exponentiations in the slower group G2
		//since a*b = b*a, we swap in case
		if len(g.rightIns) > len(g.leftIns) {
			tmp := g.rightIns
			g.rightIns = g.leftIns
			g.leftIns = tmp
		}

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

			cConstraint.Insert(uint(indexMap[g.arithmeticRepresentatnt.Identifier]), big.NewInt(int64(1)))

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
			aConstraint.Insert(uint(indexMap[g.identifier]), big.NewInt(int64(1)))
			bConstraint.Insert(uint(indexMap[g.identifier]), big.NewInt(int64(1)))
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

		insertValue(factor{typ: Token{Identifier: randInput}, multiplicative: bigOne}, aConstraint)
		insertValue(factor{typ: Token{Identifier: randInput}, multiplicative: bigOne}, bConstraint)
		insertValue(factor{typ: Token{Identifier: randInput}, multiplicative: bigOne}, eConstraint)
		insertValue(factor{typ: Token{Identifier: randOutput}, multiplicative: bigOne}, cConstraint)

		r1CS.L = append(r1CS.L, aConstraint)
		r1CS.R = append(r1CS.R, bConstraint)
		r1CS.E = append(r1CS.E, eConstraint)
		r1CS.O = append(r1CS.O, cConstraint)
	}
	r1CS.NumberOfGates = len(r1CS.L)
	r1CS.WitnessLength = len(indexMap)
	return
}
