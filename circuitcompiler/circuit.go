package circuitcompiler

import (
	"fmt"
	"math/big"
)

var variableIndicationSign = "@"

// Circuit is the data structure of the compiled circuit
type Circuit struct {
	Name      string
	Inputs    []string //the inputs of a circuit are circuits. Tis way we can pass functions as arguments
	Context   *Circuit //parent circuit. this circuit inherits all functions wich are accessible from his anchestors. Recent overload Late
	functions map[string]*Circuit

	rootConstraints *watchstack
	constraintMap   map[string]*Constraint
}

func newWatchstack() *watchstack {

	return &watchstack{
		data:     []*Constraint{},
		watchmap: make(map[string]bool),
	}

}

type watchstack struct {
	data     []*Constraint
	watchmap map[string]bool
}

func (w *watchstack) clone() (clone *watchstack) {
	clone = newWatchstack()
	for _, v := range w.data {
		clone.data = append(clone.data, v.clone())
	}
	for k, v := range w.watchmap {
		clone.watchmap[k] = v
	}
	return
}

func (w *watchstack) len() int {
	return len(w.data)
}

func (w *watchstack) remove(c *Constraint) {
	if ex := w.watchmap[c.MD5Signature()]; ex {
		delete(w.watchmap, c.MD5Signature())
		for index, k := range w.data {
			if k.MD5Signature() == c.MD5Signature() {
				if index == len(w.data)-1 {
					w.data = w.data[:index]
					return
				}
				w.data = append(w.data[:index], w.data[index+1:]...)
			}
		}

	}
}

func (w *watchstack) add(c *Constraint) {
	if _, ex := w.watchmap[c.MD5Signature()]; !ex {
		w.watchmap[c.MD5Signature()] = true
		w.data = append(w.data, c)
	}

}

func newCircuit(name string, context *Circuit) *Circuit {
	c := &Circuit{Context: context, Name: name, constraintMap: make(map[string]*Constraint), rootConstraints: newWatchstack(), functions: make(map[string]*Circuit)}
	return c
}

func (circ *Circuit) clone() (clone *Circuit) {
	clone = newCircuit(circ.Name, circ.Context)
	clone.Inputs = circ.Inputs
	fkts := make(map[string]*Circuit)
	constr := make(map[string]*Constraint)
	for k, v := range circ.functions {
		fkts[k] = v.clone()
	}
	for k, v := range circ.constraintMap {
		constr[k] = v.clone()
	}
	clone.rootConstraints = circ.rootConstraints.clone()
	return
}

func (circ *Circuit) snapshot() (keys []string) {
	for k, _ := range circ.constraintMap {
		keys = append(keys, k)
	}
	return keys
}
func (circ *Circuit) restore(keys []string) {
	tmp := make(map[string]*Constraint)
	for _, k := range keys {
		tmp[k] = circ.constraintMap[k]
	}
	circ.constraintMap = tmp
}

func (circ *Circuit) updateRootsMap(constraint *Constraint) {

	circ._updateRootsMap(constraint)
	circ.rootConstraints.add(constraint)
}

func (circ *Circuit) _updateRootsMap(constraint *Constraint) {

	for _, v := range constraint.Inputs {
		circ._updateRootsMap(v)
		circ.rootConstraints.remove(v)
	}

}

func (circ *Circuit) semanticCheck_RootMapUpdate(constraint *Constraint) *Constraint {

	if v, ex := circ.constraintMap[constraint.Output.Identifier]; !ex {
		if v == constraint {
			return constraint
		}
	}
	if constraint.Output.Type&(ARRAY_CALL|ARGUMENT|NumberToken|Operator) != 0 {
		return constraint
	}
	for i := 0; i < len(constraint.Inputs); i++ {
		constraint.Inputs[i] = circ.semanticCheck_RootMapUpdate(constraint.Inputs[i])
	}

	switch constraint.Output.Type {
	case IF:
		return constraint
	case ELSE:
		return constraint
	case VARIABLE_OVERLOAD:
		//TODO should we allow overload from a ancstor variable
		if _, ex := circ.constraintMap[constraint.Output.Identifier]; !ex {
			panic(fmt.Sprintf("variable %s not declared", constraint.Output.Identifier))
		}
		circ.constraintMap[constraint.Output.Identifier] = constraint
		break
	case FUNCTION_CALL:
		//if _, ex := circ.findFunctionInBloodline(constraint.Output.Identifier); !ex {
		//	panic(fmt.Sprintf("function %s not declared", constraint.Output.Identifier))
		//}
		break
	case VARIABLE_DECLARE:
		if _, ex := circ.constraintMap[constraint.Output.Identifier]; ex {
			panic(fmt.Sprintf("variable %s already declared", constraint.Output.Identifier))
		}
		(constraint.Output.Type) = UNASIGNEDVAR

		circ.constraintMap[constraint.Output.Identifier] = constraint
		break

	case ARRAY_Define:

		for i := 0; i < len(constraint.Inputs); i++ {
			element := fmt.Sprintf("%s[%v]", constraint.Output.Identifier, i)
			circ.constraintMap[element] = constraint.Inputs[i]
		}
		return constraint
	case RETURN:
		//constraint.Output.Identifier= fmt.Sprintf("%s%v",circ.Name,len(constraint.Output.Identifier))
		constraint.Output.Identifier = circ.Name

		break
	case UNASIGNEDVAR:
		//TODO break or return
		break
	case IdentToken:
		if v, ex := circ.findConstraintInBloodline(constraint.Output.Identifier); ex {
			return v
		}
		panic(fmt.Sprintf("variable %s used but not declared", constraint.Output.Identifier))
		//circ.constraintMap[constraint.Output.Identifier] = constraint
		break
	default:
		panic(fmt.Sprintf("not implemented %v", constraint))

	}
	circ.updateRootsMap(constraint)
	return constraint
}

func RegisterFunctionFromConstraint(constraint *Constraint, context *Circuit) (c *Circuit) {

	name := constraint.Output.Identifier
	c = newCircuit(name, context)

	for _, arg := range constraint.Inputs {
		c.Inputs = append(c.Inputs, arg.Output.Identifier)
		if _, ex := c.functions[arg.Output.Identifier]; ex {
			panic("argument must be unique ")
		}
		cl := arg.clone()
		cl.Output.Type = FUNCTION_CALL
		//we say its a function call, but we dont say how many arguments this function takes.
		c.constraintMap[arg.Output.Identifier] = cl
		//TODO
		rmp := newCircuit(arg.Output.Identifier, nil)
		rmp.updateRootsMap(arg)
		c.functions[arg.Output.Identifier] = rmp
	}

	return
}

func splitAtIfEnd(cs []*Constraint) (inside, outside []*Constraint, success bool) {

	ctr := 0

	for i, c := range cs {
		if c.Output.Type == IF {
			ctr++
		}
		if c.Output.Type == IF_ELSE_CHAIN_END {
			ctr--
		}
		if ctr == 0 {
			if i == len(cs)-1 {
				return cs[:i], outside, true
			}
			return cs[:i], cs[i+1:], true
		}
	}
	return
}

func splitAtNestedEnd(cs []*Constraint) (insideNested, outsideNested []*Constraint, success bool) {

	ctr := 0

	for i, c := range cs {
		if c.Output.Type == ELSE || c.Output.Type == FOR || c.Output.Type == FUNCTION_DEFINE || c.Output.Type == IF {
			ctr++
		}
		if c.Output.Type == NESTED_STATEMENT_END {
			ctr--
		}
		if ctr == 0 {
			if i == len(cs)-1 {
				return cs[0:i], outsideNested, true
			}
			return cs[0:i], cs[i+1:], true
		}
	}
	return
}

func (currentCircuit *Circuit) checkStaticCondition(c *Constraint) (isSatisfied bool) {
	//unelegant...
	if len(c.Inputs) != 3 {
		panic("not a condition")
	}
	var factorsA, factorsB factors
	var varEndA, varEndB bool
	var A, B *big.Int

	factorsA, varEndA = currentCircuit.compile(c.Inputs[1], newGateContainer())
	factorsB, varEndB = currentCircuit.compile(c.Inputs[2], newGateContainer())

	A = factorsA[0].multiplicative
	B = factorsB[0].multiplicative

	if varEndA || varEndB {
		panic("no dynamic looping supported")
	}
	switch c.Inputs[0].Output.Identifier {
	case "==":
		if A.Cmp(B) != 0 {
			return false
		}
		break
	case "!=":
		if A.Cmp(B) == 0 {
			return false
		}
		break
	case ">":
		if A.Cmp(B) != 1 {
			return false
		}
		break
	case ">=":
		if A.Cmp(B) == -1 {
			return false
		}
		break
	case "<":
		if A.Cmp(B) != -1 {
			return false
		}
		break
	case "<=":
		if A.Cmp(B) == 1 {
			return false
		}
		break
	default:
		panic(c.Inputs[0].Output.String())

	}
	return true
}

//unpack loops, decide static if conditions
func (currentCircuit *Circuit) preCompile(constraintStack []*Constraint) {
	if len(constraintStack) == 0 {
		return
	}
	currentConstraint := constraintStack[0]
	switch currentConstraint.Output.Type {
	case IF:
		insideIf, outsideIf, succ := splitAtIfEnd(constraintStack)
		constraintStack = outsideIf

		if !succ {
			panic("unexpected, should be detected at parsing")
		}

		condition, rest, succ2 := splitAtNestedEnd(insideIf)
		if !succ2 {
			panic("unexpected, should be detected at parsing")
		}
		//if and else if
		if currentCircuit.checkStaticCondition(currentConstraint.Inputs[0]) {
			snap2 := currentCircuit.snapshot()
			currentCircuit.preCompile(condition[1:])
			currentCircuit.restore(snap2)
			currentCircuit.preCompile(constraintStack)
			return
		}
		currentCircuit.preCompile(rest)
		currentCircuit.preCompile(constraintStack)
		return
	case ELSE:
		//else only
		if len(currentConstraint.Inputs) == 0 {
			snap2 := currentCircuit.snapshot()
			currentCircuit.preCompile(constraintStack[1:])
			currentCircuit.restore(snap2)
			return
		}

		condition, rest, succ2 := splitAtNestedEnd(constraintStack)
		if !succ2 {
			panic("unexpected, should be detected at parsing")
		}
		//if and else if
		if currentCircuit.checkStaticCondition(currentConstraint.Inputs[0]) {
			snap2 := currentCircuit.snapshot()
			currentCircuit.preCompile(condition[1:])
			currentCircuit.restore(snap2)
			return
		}
		currentCircuit.preCompile(rest)
		return
	case IF_ELSE_CHAIN_END:
		break
	case FUNCTION_DEFINE:
		insideFunc, outsideFunc, succ := splitAtNestedEnd(constraintStack)
		if !succ {
			panic("unexpected, should be detected at parsing")
		}
		if _, ex := currentCircuit.functions[currentConstraint.Output.Identifier]; ex {
			panic(fmt.Sprintf("function %s already declared", currentConstraint.Output.Identifier))
		}
		if _, ex := currentCircuit.constraintMap[currentConstraint.Output.Identifier]; ex {
			panic(fmt.Sprintf("function %s overloads variable with same name", currentConstraint.Output.Identifier))
		}
		newFunc := RegisterFunctionFromConstraint(currentConstraint, currentCircuit)
		currentCircuit.functions[currentConstraint.Output.Identifier] = newFunc
		currentCircuit.constraintMap[currentConstraint.Output.Identifier] = &Constraint{
			Output: Token{
				Type:       FUNCTION_CALL,
				Identifier: currentConstraint.Output.Identifier,
			},
			Inputs: currentConstraint.Inputs,
		}

		//NOTE this happens now during compilation
		//for k, v := range currentCircuit.constraintMap {
		//	//we keep the arguments this way
		//	if _, ex := newFunc.constraintMap[k]; !ex {
		//		newFunc.constraintMap[k] = v
		//	}
		//}
		newFunc.preCompile(insideFunc[1:])
		currentCircuit.preCompile(outsideFunc)
		return
	case FOR:
		//gather stuff, then evaluate
		insideFor, outsideFor, succ := splitAtNestedEnd(constraintStack)
		if !succ {
			panic("unexpected, should be detected at parsing")
		}
		if len(insideFor) == 0 {
			currentCircuit.preCompile(outsideFor)
			return
		}
		for {
			if !currentCircuit.checkStaticCondition(currentConstraint.Inputs[0]) {
				break
			}
			snap2 := currentCircuit.snapshot()
			currentCircuit.preCompile(insideFor[1:])
			//allow overwriting of variables declared within the loop body
			currentCircuit.restore(snap2)
			//call the increment condition
			currentCircuit.semanticCheck_RootMapUpdate(currentConstraint.Inputs[1].clone())
		}
		//cut of the part within the for loop
		currentCircuit.preCompile(outsideFor)
		return
	case NESTED_STATEMENT_END:
		//skippp over
		break
	default:
		currentCircuit.semanticCheck_RootMapUpdate(constraintStack[0].clone())

	}
	currentCircuit.preCompile(constraintStack[1:])
}

//clone returns a deep copy of c
func (c *Constraint) clone() *Constraint {
	in := make([]*Constraint, len(c.Inputs))
	for i, cc := range c.Inputs {
		in[i] = cc.clone()
	}
	return &Constraint{
		Output: c.Output,
		Inputs: in,
	}
}
