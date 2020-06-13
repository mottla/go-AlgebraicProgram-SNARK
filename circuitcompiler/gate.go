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
	additionGate
	sumCheckGate
	zeroOrOneGate
)

type Gate struct {
	gateType    gateType
	value       MultiplicationGateSignature
	leftIns     factors //leftIns and RightIns after addition gates have been reduced. only multiplication gates remain
	rightIns    factors
	expoIns     factors
	outIns      factors
	output      *big.Int
	noNewOutput bool
	//only for yero or one gates. they carry the information
	arithmeticRepresentatnt Token
}

func (g Gate) String() string {
	return fmt.Sprintf("Gate: %v  with left %v right %v", g.value.commonExtracted, g.leftIns, g.rightIns)
}
