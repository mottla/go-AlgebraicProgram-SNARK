package circuitcompiler

import (
	"fmt"
	"sort"
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

func (gate *Gate) ID() (id string) {
	if gate.identifier == "" {
		return gate.setAndGetID()
	}
	return gate.identifier
}

func (gate *Gate) setAndGetID() (id string) {

	sort.Sort(gate.leftIns)
	sort.Sort(gate.rightIns)
	lr := append(gate.leftIns, gate.rightIns...)
	sort.Sort(gate.expoIns)
	sort.Sort(gate.outIns)
	ID := hashFactorsToBig(append(append(gate.expoIns, lr...), gate.outIns...))
	gate.identifier = ID.String()[:16]
	return gate.identifier
}
func (gate *Gate) minimizeR1CSDescriptiveComplexity() {

	//g^(e1+e2+..) + (r1+r2+..)*(l1+l2+..) = (c1+c2+..)
	//if g^e is 0, we can try if the constraint
	//l * 1/c = 1/r  or
	//r * 1/c = 1/l  or
	//r * 1/c = 1/l  or
	//1/r*1/l=1/c
	//is the better represenant regarding bit complexity
	if gate.expoIns == nil {
		//rInv, lInv, cInv := invertFactors(gate.leftIns), invertFactors(gate.rightIns), invertFactors(gate.outIns)

	}
}
