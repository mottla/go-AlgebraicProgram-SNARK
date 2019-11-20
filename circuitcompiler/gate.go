package circuitcompiler

import (
	"errors"
	"fmt"
)

type gateType uint8

const (
	mgate gateType = 1
	egate gateType = 2
)

type Gate struct {
	gateType gateType
	index    int
	left     *Gate
	right    *Gate
	//funcInputs []*Gate
	value    *Constraint //is a pointer a good thing here??
	leftIns  factors     //leftIns and RightIns after addition gates have been reduced. only multiplication gates remain
	rightIns factors
	expoIns  factors
}

func (g Gate) String() string {
	return fmt.Sprintf("Gate %v : %v  with left %v right %v", g.index, g.value, g.leftIns, g.rightIns)
}

func (g *Gate) ExtractValues(in []int) (er error) {
	if b, v1 := isValue(g.value.V1); b {
		if b2, v2 := isValue(g.value.V2); b2 {
			in = append(in, v1, v2)
			return nil
		}
	}
	return errors.New(fmt.Sprintf("Gate \"%s\" has no int values", g.value))
}

func (g *Gate) OperationType() Token {
	return g.value.Op
}

//copies a Gate neglecting its references to other gates
func cloneGate(in *Gate) (out *Gate) {
	constr := &Constraint{Inputs: in.value.Inputs, Out: in.value.Out, Op: in.value.Op, invert: in.value.invert, negate: in.value.negate, V2: in.value.V2, V1: in.value.V1}
	nRightins := in.rightIns.clone()
	nLeftInst := in.leftIns.clone()
	return &Gate{value: constr, leftIns: nLeftInst, rightIns: nRightins, index: in.index}
}
