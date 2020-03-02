package circuitcompiler

import (
	"fmt"
	"math/big"
)

var variableIndicationSign = "@"

// function is the data structure of the compiled circuit
type function struct {
	Name string

	Inputs []string //the inputs of a circuit are circuits. Tis way we can pass functions as arguments

	Outputs []string

	//parent function. this function inherits all functions wich are accessible from his anchestors. Recent overload Late
	Context *function

	//this are the functions, that are defined within this function
	functions map[string]*function

	//this will stay. the concept of a taskstack is relevant
	taskStack *watchstack
	//lets turn this into something we only need for the semantic check
	constraintMap map[string]*Constraint
}

type watchstack struct {
	data []*Constraint
}

func newCircuit(name string, context *function) *function {
	c := &function{Context: context, Name: name, constraintMap: make(map[string]*Constraint), taskStack: newWatchstack(), functions: make(map[string]*function)}
	return c
}

func RegisterFunctionFromConstraint(constraint *Constraint, context *function) (c *function) {

	name := constraint.Output.Identifier
	c = newCircuit(name, context)

	for _, arg := range constraint.Inputs {
		c.Inputs = append(c.Inputs, arg.Output.Identifier)
		if _, ex := c.functions[arg.Output.Identifier]; ex {
			panic("argument must be unique ")
		}

		cl := arg.clone()
		cl.Output.Type = FUNCTION_CALL
		c.constraintMap[arg.Output.Identifier] = cl
		//if i add them as functions, then they later can be replaced by functions.
		rmp := newCircuit(arg.Output.Identifier, nil)
		rmp.taskStack.add(&Constraint{
			Output: Token{
				Type:       RETURN,
				Identifier: "",
			},
			Inputs: []*Constraint{arg},
		})

		c.functions[arg.Output.Identifier] = rmp
	}

	return
}

//unpack loops, decide static if conditions
//lets get dynamic bitch
func (currentCircuit *function) preCompile(constraintStack []*Constraint) {
	if len(constraintStack) == 0 {
		return
	}
	currentConstraint := constraintStack[0]
	switch currentConstraint.Output.Type {
	case IF:
		entireIfElse, outsideIfElse := splitAtIfEnd(constraintStack)

		identifier := fmt.Sprintf("%vif", currentCircuit.taskStack.len())

		newFunc := newCircuit(identifier, currentCircuit)

		currentCircuit.functions[identifier] = newFunc
		currentCircuit.taskStack.add(&Constraint{
			Output: Token{
				Type:       FUNCTION_CALL,
				Identifier: identifier,
			},
		})

		firstIf, elseAndRest, succ2 := splitAtNestedEnd(entireIfElse)
		if !succ2 {
			panic("unexpected, should be detected at parsing")
		}

		identifier2 := fmt.Sprintf("%vif", newFunc.taskStack.len())
		ifcircuit := newCircuit("if", currentCircuit)

		newFunc.functions[identifier2] = ifcircuit

		newFunc.taskStack.add(&Constraint{
			Output: Token{
				Type:       IF,
				Identifier: identifier2,
			},
			Inputs: firstIf[0].Inputs,
		})
		currentCircuit.preCompile(outsideIfElse)
		ifcircuit.preCompile(firstIf[1:])
		newFunc.preCompile(elseAndRest)

		return
	case ELSE:

		firstIf, elseAndRest, succ2 := splitAtNestedEnd(constraintStack)
		if !succ2 {
			panic("unexpected, should be detected at parsing")
		}

		identifier2 := fmt.Sprintf("%vif", currentCircuit.taskStack.len())

		ifcircuit := newCircuit("else", currentCircuit)

		currentCircuit.functions[identifier2] = ifcircuit

		currentCircuit.taskStack.add(&Constraint{
			Output: Token{
				Type:       IF,
				Identifier: identifier2,
			},
			Inputs: firstIf[0].Inputs,
		})
		currentCircuit.preCompile(elseAndRest)
		ifcircuit.preCompile(firstIf[1:])

		return
	case IF_ELSE_CHAIN_END:
		break
	case ARRAY_DECLARE:
		if _, ex := currentCircuit.constraintMap[currentConstraint.Output.Identifier]; ex {
			panic(fmt.Sprintf("array %s already declared", currentConstraint.Output.Identifier))
		}
		currentCircuit.constraintMap[currentConstraint.Output.Identifier] = currentConstraint

		for i := 0; i < len(currentConstraint.Inputs); i++ {
			element := fmt.Sprintf("%s[%v]", currentConstraint.Output.Identifier, i)
			constr := &Constraint{
				Output: Token{
					Type:       VARIABLE_DECLARE,
					Identifier: element,
				},
				Inputs: []*Constraint{currentConstraint.Inputs[i]},
			}
			currentCircuit.preCompile([]*Constraint{constr})
		}
	case VARIABLE_DECLARE:
		if _, ex := currentCircuit.functions[currentConstraint.Output.Identifier]; ex {
			panic(fmt.Sprintf("variable %s already declared", currentConstraint.Output.Identifier))
		}
		rmp := newCircuit(currentConstraint.Output.Identifier, currentCircuit)
		rmp.taskStack.add(&Constraint{
			Output: Token{
				Type:       RETURN,
				Identifier: "",
			},
			Inputs: currentConstraint.Inputs,
		},
		)
		currentCircuit.functions[currentConstraint.Output.Identifier] = rmp
		currentCircuit.constraintMap[currentConstraint.Output.Identifier] = &Constraint{
			Output: Token{
				Type:       FUNCTION_CALL,
				Identifier: currentConstraint.Output.Identifier,
			},
		}
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
				Type:       FUNCTION_CALL, //if someone accesses the function, he does not necessarily want to call it
				Identifier: currentConstraint.Output.Identifier,
			},
			//Inputs: currentConstraint.Inputs,
		}
		currentCircuit.preCompile(outsideFunc)
		newFunc.preCompile(insideFunc[1:])
		return
	case FOR:
		//gather stuff, then evaluate
		insideFor, outsideFor, succ := splitAtNestedEnd(constraintStack)
		if !succ {
			panic("unexpected, should be detected at parsing")
		}

		identifier2 := fmt.Sprintf("%vfor", currentCircuit.taskStack.len())

		forCircuit := newCircuit("for", currentCircuit)

		currentCircuit.functions[identifier2] = forCircuit

		currentCircuit.taskStack.add(&Constraint{
			Output: Token{
				Type:       FOR,
				Identifier: identifier2,
			},
			Inputs: currentConstraint.Inputs,
		})
		currentCircuit.preCompile(outsideFor)
		forCircuit.preCompile(insideFor[1:])
		return
	case NESTED_STATEMENT_END:
		//skippp over
		break
	default:
		currentCircuit.contextCheck(constraintStack[0].clone())
		currentCircuit.taskUpdate(constraintStack[0].clone())

	}
	currentCircuit.preCompile(constraintStack[1:])
}

func (circ *function) contextCheck(constraint *Constraint) {

	if constraint.Output.Type&(NumberToken|Operator) != 0 {
		return
	}
	for i := 0; i < len(constraint.Inputs); i++ {
		circ.contextCheck(constraint.Inputs[i])
	}

	switch constraint.Output.Type {
	case ARGUMENT:
		if _, ex := circ.constraintMap[constraint.Output.Identifier]; !ex {
			panic(fmt.Sprintf("variable %s not found", constraint.Output.Identifier))
		}
	case VARIABLE_OVERLOAD:

	case FUNCTION_CALL:
		//if _, ex := circ.findFunctionInBloodline(constraint.Output.Identifier); !ex {
		//	panic(fmt.Sprintf("function %s used but not declared", constraint.Output.Identifier))
		//}
	case VARIABLE_DECLARE:
		if _, ex := circ.constraintMap[constraint.Output.Identifier]; ex {
			panic(fmt.Sprintf("variable %s already declared", constraint.Output.Identifier))
		}
	case ARRAY_DECLARE:
		if _, ex := circ.constraintMap[constraint.Output.Identifier]; ex {
			panic(fmt.Sprintf("array %s already declared", constraint.Output.Identifier))
		}
	case IDENTIFIER_VARIABLE:
		if _, ex := circ.findConstraintInBloodline(constraint.Output.Identifier); !ex {
			panic(fmt.Sprintf("variable %s used but not declared", constraint.Output.Identifier))
		}
	case ARRAY_CALL:
		if c, ex := circ.findConstraintInBloodline(constraint.Output.Identifier); !ex || c.Output.Type != ARRAY_DECLARE {
			panic(fmt.Sprintf("array %s not declared", constraint.Output.Identifier))
		}
	default:

	}

	return
}

func (circ *function) taskUpdate(constraint *Constraint) {

	switch constraint.Output.Type {
	case VARIABLE_OVERLOAD:
		//TODO Is overloading a task?
		circ.taskStack.add(constraint)

	case FUNCTION_CALL:
		//since function does not need to be defined, we do nothing
		circ.taskStack.add(constraint)
	case ARRAY_DECLARE:

		circ.constraintMap[constraint.Output.Identifier] = constraint

		for i := 0; i < len(constraint.Inputs); i++ {
			element := fmt.Sprintf("%s[%v]", constraint.Output.Identifier, i)
			constr := &Constraint{
				Output: Token{
					Type:       VARIABLE_DECLARE,
					Identifier: element,
				},
				Inputs: []*Constraint{constraint.Inputs[i]},
			}
			circ.taskUpdate(constr)
		}

	case RETURN:
		circ.taskStack.add(constraint)
	default:

	}

	return
}

func (currentCircuit *function) findFunctionInBloodline(identifier string) (*function, bool) {
	if currentCircuit == nil {
		return nil, false
	}
	if con, ex := currentCircuit.functions[identifier]; ex {
		return con, true
	}
	return currentCircuit.Context.findFunctionInBloodline(identifier)

}

//TODO maybe I add context to every constraint as its done with the functions. in the ende everything is a function anyways
func (currentCircuit *function) findConstraintInBloodline(identifier string) (*Constraint, bool) {
	if currentCircuit == nil {
		return nil, false
	}
	if con, ex := currentCircuit.constraintMap[identifier]; ex {
		return con, true
	}
	return currentCircuit.Context.findConstraintInBloodline(identifier)

}

func (currentCircuit *function) getCircuitContainingConstraintInBloodline(identifier string) (*function, bool) {
	if currentCircuit == nil {
		return nil, false
	}
	if _, ex := currentCircuit.constraintMap[identifier]; ex {
		return currentCircuit, true
	}
	return currentCircuit.Context.getCircuitContainingConstraintInBloodline(identifier)

}

func (circ *function) clone() (clone *function) {
	if circ == nil || circ.Context == nil {
		return nil
	}
	clone = newCircuit(circ.Name, circ.Context.clone())
	clone.Inputs = circ.Inputs
	for k, v := range circ.functions {
		clone.functions[k] = v.clone()
	}
	for k, v := range circ.constraintMap {
		clone.constraintMap[k] = v.clone()
	}
	clone.taskStack = circ.taskStack.clone()
	return
}

func (circ *function) snapshot() (keys []string) {
	for k, _ := range circ.constraintMap {
		keys = append(keys, k)
	}
	return keys
}
func (circ *function) restore(keys []string) {
	tmp := make(map[string]*Constraint)
	for _, k := range keys {
		tmp[k] = circ.constraintMap[k]
	}
	circ.constraintMap = tmp
}

//func (circ *function) updateRootsMap(constraint *Constraint) {
//
//	circ._updateRootsMap(constraint)
//	circ.taskStack.add(constraint)
//}
//
//func (circ *function) _updateRootsMap(constraint *Constraint) {
//
//	for _, v := range constraint.Inputs {
//		circ._updateRootsMap(v)
//		circ.taskStack.remove(v)
//	}
//
//}

func (currentCircuit *function) checkStaticCondition(c *Constraint) (isSatisfied bool) {
	//unelegant...

	var factorsA, factorsB factors
	var varEndA, varEndB bool
	var A, B *big.Int

	factorsA, varEndA, _ = currentCircuit.compile(c.Inputs[1], newGateContainer())
	factorsB, varEndB, _ = currentCircuit.compile(c.Inputs[2], newGateContainer())

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

func newWatchstack() *watchstack {

	return &watchstack{
		data: []*Constraint{},
	}

}

//func (w *watchstack) iterate() (iterator chan *Constraint){
//	iterator = make(chan *Constraint)
//	go func() {
//		for _,v:= range w.data{
//			iterator <-v
//		}
//		close(iterator)
//	}()
//	return
//}

func (w *watchstack) clone() (clone *watchstack) {
	clone = newWatchstack()
	for _, v := range w.data {
		clone.data = append(clone.data, v.clone())
	}
	return
}

func (w *watchstack) len() int {
	return len(w.data)
}

func (w *watchstack) add(c *Constraint) {
	w.data = append(w.data, c)

}

//func (w *watchstack) remove(c *Constraint) {
//	if ex := w.watchmap[c.MD5Signature()]; ex {
//		delete(w.watchmap, c.MD5Signature())
//		for index, k := range w.data {
//			if k.MD5Signature() == c.MD5Signature() {
//				if index == len(w.data)-1 {
//					w.data = w.data[:index]
//					return
//				}
//				w.data = append(w.data[:index], w.data[index+1:]...)
//			}
//		}
//
//	}
//}
//
//func (w *watchstack) add(c *Constraint) {
//	if _, ex := w.watchmap[c.MD5Signature()]; !ex {
//		w.watchmap[c.MD5Signature()] = true
//		w.data = append(w.data, c)
//	}
//
//}
func splitAtIfEnd(cs []*Constraint) (inside, outside []*Constraint) {

	for i, v := range cs {
		if v.Output.Type == IF_ELSE_CHAIN_END {
			return cs[:i], cs[i:]
		}
	}
	panic("unexpected reach")
	return inside, outside
}

//func splitAtIfEnd(cs []*Constraint) (inside, outside []*Constraint) {
//
//	closeConstraint := &Constraint{
//		Output: Token{
//			Type: NESTED_STATEMENT_END,
//		},
//	}
//	var firstIf []*Constraint
//	firstIf, outside, _ = splitAtNestedEnd(cs)
//	inside = append(inside, firstIf...)
//
//	firstIf, outside, _ = splitAtNestedEnd(outside)
//	for ; len(firstIf) > 0 && firstIf[0].Output.Type == ELSE;  firstIf, outside, _ = splitAtNestedEnd(outside) {
//		inside = append(inside, closeConstraint)
//		inside = append(inside, firstIf...)
//	}
//	inside = append(inside, closeConstraint)
//	return inside, outside
//}

func splitAtIfElseEnd(cs []*Constraint) (insideIf, outsideNested []*Constraint, success bool) {

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
