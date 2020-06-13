package circuitcompiler

import (
	"fmt"
)

type gateType uint8

const (
	multiplicationGate gateType = iota
	returnMultiplicationGate

	scalarBaseMultiplyGate
	equalityGate
	additionGate
	sumCheckGate
	zeroOrOneGate
)

type Gate struct {
	gateType   gateType
	identifier string
	leftIns    factors //leftIns and RightIns after addition gates have been reduced. only multiplication gates remain
	rightIns   factors
	expoIns    factors
	outIns     factors
	//extractedConstants *big.Int
	noNewOutput bool
	//only for yero or one gates. they carry the information
	arithmeticRepresentatnt Token
}

func (g Gate) String() string {
	return fmt.Sprintf("Gate: %v  with left %v right %v", g.identifier, g.leftIns, g.rightIns)
}
