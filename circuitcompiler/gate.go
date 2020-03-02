package circuitcompiler

import (
	"fmt"
	"math/big"
)

type gateType uint8

const (
	multiplicationGate gateType = iota
	scalarBaseMultiplyGate
	equalityGate
)

type Gate struct {
	gateType gateType
	value    MultiplicationGateSignature
	leftIns  factors //leftIns and RightIns after addition gates have been reduced. only multiplication gates remain
	rightIns factors
	expoIns  factors
	output   *big.Int
}

func (g Gate) String() string {
	return fmt.Sprintf("Gate: %v  with left %v right %v", g.value.commonExtracted, g.leftIns, g.rightIns)
}
