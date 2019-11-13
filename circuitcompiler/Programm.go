package circuitcompiler

import (
	"crypto/sha256"
	"fmt"
	"github.com/mottla/go-AlgebraicProgram-SNARK/circuitcompiler/fields"
	"math/big"
)

type Fields struct {
	ArithmeticField fields.Fq
	PolynomialField fields.PolynomialField
	CurveOrderField fields.Fq
}

type MultiplicationGateSignature struct {
	identifier      string
	commonExtracted [2]int //if the mgate had a extractable factor, it will be stored here
}

type Program struct {
	functions    map[string]*Circuit
	globalInputs []*Gate
	Fields       Fields //find a better name

	//key 1: the hash chain indicating from where the variable is called H( H(main(a,b)) , doSomething(x,z) ), where H is a hash function.
	//value 1 : map
	//			with key variable name
	//			with value variable name + hash Chain
	//this datastructure is nice but maybe ill replace it later with something less confusing
	//it serves the elementary purpose of not computing a variable a second time.
	//it boosts parse time
	computedInContext map[string]map[string]MultiplicationGateSignature

	//to reduce the number of multiplication gates, we store each factor signature, and the variable name,
	//so each time a variable is computed, that happens to have the very same factors, we reuse the former
	//it boost setup and proof time
	computedFactors map[string]MultiplicationGateSignature
}

func PrepareFields(CurveOrder, FieldOrder *big.Int) Fields {
	// new Finite Field
	fqR := fields.NewFq(FieldOrder)
	// new Polynomial Field
	pf := fields.NewPolynomialFieldPrecomputedLagriangian(fqR, 0)

	return Fields{
		ArithmeticField: fqR,
		PolynomialField: *pf,
		CurveOrderField: fields.NewFq(CurveOrder),
	}
}

func NewProgram(CurveOrder, FieldOrder *big.Int) (p *Program) {
	p = &Program{
		functions:    map[string]*Circuit{},
		globalInputs: []*Gate{{value: &Constraint{Op: CONST, Out: "1"}}},
		Fields:       PrepareFields(CurveOrder, FieldOrder),
	}

	//pointMultiplicationCircuit :=&Circuit{Name:"Exp"}
	//p.functions["g"] = &Circuit{Name: "Exp"}
	return
}

//returns the cardinality of all main inputs + 1 for the "one" signal
func (p *Program) GlobalInputCount() int {
	return len(p.globalInputs)
}

func (p *Program) PrintContraintTrees() {
	for k, v := range p.functions {
		fmt.Println(k)
		PrintTree(v.root)
	}
}

func (p *Program) PrintConstaintTree() {
	for k, v := range p.functions {
		fmt.Println(k)
		PrintTree(v.root)
	}
}

func (p *Program) BuildConstraintTrees() {

	mainRoot := p.getMainCircuit().root

	//if our programs last operation is not a multiplication Gate, we need to introduce on
	if mainRoot.value.Op&(MINUS|PLUS) != 0 {
		newOut := Constraint{Out: "out", V1: "1", V2: "out2", Op: MULTIPLY}
		p.getMainCircuit().prepareAndAddConstraintToGateMap(&newOut)
		mainRoot.value.Out = "out2"
		p.getMainCircuit().gateMap[mainRoot.value.Out] = mainRoot
	}

	p.globalInputs = append(p.globalInputs, p.getMainCircuit().Inputs...)

	//var wg = sync.WaitGroup{}

	//we build the parse trees concurrently! because we can! go rocks
	for _, circuit := range p.functions {
		//wg.Add(1)
		////interesting: if circuit is not passed as argument, the program fails. duno why..
		//go func(c *Circuit) {
		//	c.buildTree(c.root)
		//	wg.Done()
		//}(circuit)
		circuit.buildTree(circuit.root)
	}
	//wg.Wait()
	return

}

func (c *Circuit) isArgument(in string) (isArg bool, constraint *Constraint) {
	for _, v := range c.Inputs {
		if v.value.Out == in {
			return true, v.value
		}
	}
	return false, nil
}

func (c *Circuit) buildTree(g *Gate) {

	//if g.OperationType() == CONST {
	//	return
	//}
	if b, v := c.isArgument(g.value.Out); b {
		g.value = v
		return
	}

	if g.OperationType() == FUNC {
		for _, ingate := range g.value.Inputs {
			c.buildTree(ingate)
		}
		return
	}

	if gate, ex := c.gateMap[g.value.V1]; ex {
		g.left = gate
		c.buildTree(gate)
	}
	if gate, ex := c.gateMap[g.value.V2]; ex {
		g.right = gate
		c.buildTree(gate)
	}

}

func (p *Program) ReduceCombinedTree() (orderedmGates []Gate) {
	orderedmGates = []Gate{}
	p.computedInContext = make(map[string]map[string]MultiplicationGateSignature)
	p.computedFactors = make(map[string]MultiplicationGateSignature)
	rootHash := make([]byte, 10)
	p.computedInContext[string(rootHash)] = make(map[string]MultiplicationGateSignature)
	p.r1CSRecursiveBuild(p.getMainCircuit(), p.getMainCircuit().root, rootHash, &orderedmGates, false, false)
	return orderedmGates
}

//recursively walks through the parse tree to create a list of all
//multiplication gates needed for the QAP construction
//Takes into account, that multiplication with constants and addition (= substraction) can be reduced, and does so
func (p *Program) r1CSRecursiveBuild(currentCircuit *Circuit, currentGate *Gate, hashTraceBuildup []byte, orderedmGates *[]Gate, negate bool, invert bool) (facs factors, hashTraceResult []byte, variableEnd bool) {

	if out, ex := p.computedInContext[string(hashTraceBuildup)][currentGate.value.Out]; ex {
		fac := &factor{typ: IN, name: out.identifier, invert: invert, negate: negate, multiplicative: out.commonExtracted}
		return factors{fac}, hashTraceBuildup, true
	}

	if currentGate.OperationType() == CONST {
		b1, v1 := isValue(currentGate.value.Out)
		if !b1 {
			panic("not a constant")
		}
		mul := [2]int{v1, 1}
		if invert {
			mul = [2]int{1, v1}
		}
		//return factors{{typ: CONST, negate: negate, multiplicative: mul}}, hashTraceBuildup, false
		return factors{{typ: CONST, negate: negate, multiplicative: mul}}, hashTraceBuildup, false
	}

	if currentGate.OperationType() == FUNC {
		//TODO g handling
		_, n, _ := isFunction(currentGate.value.Out)
		if n == "g" {
			expGate := &Gate{gateType: egate, value: currentGate.value, index: len(*orderedmGates), expoIns: factors{{typ: EXP, name: currentGate.value.Inputs[0].value.Out, multiplicative: [2]int{1, 1}}}}
			p.computedInContext[string(hashTraceBuildup)][currentGate.value.Out] = MultiplicationGateSignature{commonExtracted: [2]int{1, 1}, identifier: currentGate.value.Out}
			//p.computedFactors[sig.identifier] = MultiplicationGateSignature{identifier: rootGate.value.Out, commonExtracted: sig.commonExtracted}
			*orderedmGates = append(*orderedmGates, *expGate)
			return factors{{typ: IN, name: currentGate.value.Out, negate: negate, invert: invert, multiplicative: [2]int{1, 1}}}, hashTraceBuildup, true
		}
		//changes the leaves of a circuit (which are the inputs and constants) to the arguments passed
		nextContext := p.changeInputs(currentGate.value)
		currentCircuit = nextContext
		currentGate = nextContext.root
		hashTraceBuildup = hashTogether(hashTraceBuildup, []byte(currentCircuit.currentOutputName()))
		if _, ex := p.computedInContext[string(hashTraceBuildup)]; !ex {
			p.computedInContext[string(hashTraceBuildup)] = make(map[string]MultiplicationGateSignature)
		}
	}

	if currentGate.OperationType() == IN {
		//fac := &factor{typ: IN, name: currentGate.value.Out, invert: invert, negate: negate, multiplicative: [2]int{1, 1}}
		fac := &factor{typ: IN, name: currentGate.value.Out, invert: invert, multiplicative: [2]int{1, 1}}
		return factors{fac}, hashTraceBuildup, true
	}

	leftFactors, hashLeft, variableEnd := p.r1CSRecursiveBuild(currentCircuit, currentGate.left, hashTraceBuildup, orderedmGates, negate, invert)

	rightFactors, hashRight, cons := p.r1CSRecursiveBuild(currentCircuit, currentGate.right, hashTraceBuildup, orderedmGates, Xor(negate, currentGate.value.negate), Xor(invert, currentGate.value.invert))

	if currentGate.OperationType() == MULTIPLY {

		if !(variableEnd && cons) && !currentGate.value.invert && currentGate != p.getMainCircuit().root {
			return mulFactors(leftFactors, rightFactors), hashTraceBuildup, variableEnd || cons
		}
		sig, newLef, newRigh := factorsSignature(leftFactors, rightFactors)
		if out, ex := p.computedFactors[sig.identifier]; ex {
			return factors{{typ: IN, name: out.identifier, invert: invert, negate: negate, multiplicative: sig.commonExtracted}}, hashTraceBuildup, true
		}

		rootGate := cloneGate(currentGate)
		//rootGate := currentGate
		rootGate.index = len(*orderedmGates)
		if p.getMainCircuit().root == currentGate {
			newLef = mulFactors(newLef, factors{&factor{typ: CONST, multiplicative: sig.commonExtracted}})
		}

		rootGate.leftIns = newLef
		rootGate.rightIns = newRigh

		out := hashTogether(hashLeft, hashRight)
		//rootGate.value.V1 = rootGate.value.V1 //+ string(leftHash[:10])
		//rootGate.value.V2 = rootGate.value.V2 //+ string(rightHash[:10])

		rootGate.value.Out = rootGate.value.Out + string(out[:10])

		p.computedInContext[string(hashTraceBuildup)][currentGate.value.Out] = MultiplicationGateSignature{identifier: rootGate.value.Out, commonExtracted: sig.commonExtracted}

		p.computedFactors[sig.identifier] = MultiplicationGateSignature{identifier: rootGate.value.Out, commonExtracted: sig.commonExtracted}
		*orderedmGates = append(*orderedmGates, *rootGate)

		return factors{{typ: IN, name: rootGate.value.Out, invert: invert, negate: negate, multiplicative: sig.commonExtracted}}, hashTraceBuildup, true
	}

	switch currentGate.OperationType() {
	case PLUS:
		return addFactors(leftFactors, rightFactors), hashTraceBuildup, variableEnd || cons
	default:
		panic("unexpected Gate")
	}

}

//copies a Gate neglecting its references to other gates
func cloneGate(in *Gate) (out *Gate) {
	constr := &Constraint{Inputs: in.value.Inputs, Out: in.value.Out, Op: in.value.Op, invert: in.value.invert, negate: in.value.negate, V2: in.value.V2, V1: in.value.V1}
	nRightins := in.rightIns.clone()
	nLeftInst := in.leftIns.clone()
	return &Gate{value: constr, leftIns: nLeftInst, rightIns: nRightins, index: in.index}
}

func (p *Program) getMainCircuit() *Circuit {
	return p.functions["main"]
}

func (p *Program) changeInputs(constraint *Constraint) (nextContext *Circuit) {

	if constraint.Op != FUNC {
		panic("not a function")
	}
	//if _, ex := contextCircuit.gateMap[constraint.Out]; !ex {
	//	panic("constraint must be within the contextCircuit circuit")
	//}
	b, n, _ := isFunction(constraint.Out)
	if !b {
		panic("not a function")
	}
	if newContext, v := p.functions[n]; v {

		//am i certain that constraint.inputs is alwazs equal to n??? me dont like it
		for i, _ := range newContext.Inputs {
			//if
			//newContext.Inputs[i].Out = constraint.Inputs[i].Out
			//newContext.Inputs[i].Circuit = constraint.Inputs[i].Circuit
			*newContext.Inputs[i] = *constraint.Inputs[i]

		}

		//newContext.renameInputs(constraint.Inputs)
		return newContext
	}
	panic("undeclared function call. check your source")
	return nil
}

// GenerateR1CS generates the ER1CS polynomials from the Circuit
func (p *Program) GenerateReducedR1CS(mGates []Gate) (r1CS ER1CS) {
	// from flat code to ER1CS

	offset := len(p.globalInputs)
	//  one + in1 +in2+... + gate1 + gate2 .. + out
	size := offset + len(mGates)
	indexMap := make(map[string]int)

	for i, v := range p.globalInputs {
		indexMap[v.value.Out] = i
	}

	for _, v := range mGates {
		if _, ex := indexMap[v.value.Out]; !ex {
			indexMap[v.value.Out] = len(indexMap)
		}
	}

	insertValue := func(val *factor, arr []*big.Int) {
		if val.typ != CONST {
			if _, ex := indexMap[val.name]; !ex {
				panic(fmt.Sprintf("%v index not found!!!", val.name))
			}
		}
		value := p.Fields.ArithmeticField.FractionToField(val.multiplicative)
		if val.negate {
			value = p.Fields.ArithmeticField.Neg(value)
		}
		//not that index is 0 if its a constant, since 0 is the map default if no entry was found
		arr[indexMap[val.name]] = value
	}

	for _, g := range mGates {

		if g.OperationType() == MULTIPLY {
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

			cConstraint[indexMap[g.value.Out]] = big.NewInt(int64(1))

			if g.value.invert {
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

			cConstraint[indexMap[g.value.Out]] = big.NewInt(int64(1))

			if g.value.invert {
				panic("not a m Gate")
			}
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
