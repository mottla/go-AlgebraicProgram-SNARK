package circuitcompiler

import (
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
