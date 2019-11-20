package circuitcompiler

import (
	"fmt"
	bn256 "github.com/mottla/go-AlgebraicProgram-SNARK/circuitcompiler/pairing"
	//"fmt"
	////"math/big"
	//"strings"
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestXor(t *testing.T) {
	assert.Equal(t, false, Xor(true, true))
	assert.Equal(t, true, Xor(true, false))
	assert.Equal(t, true, Xor(false, true))
	assert.Equal(t, false, Xor(false, false))

}

var CircuitCorrectnessTest = []string{
	`
	def main( x  ,  z ) {
		var a = x * z
		return a*a
		}`,
}

func TestPrintTree(t *testing.T) {

	for _, test := range CircuitCorrectnessTest {

		program := NewProgram(bn256.Order, bn256.Order)

		parser := NewParser(test, false)
		parser.Parse(program)

		fmt.Println("\n unreduced")
		fmt.Println(test)

		gates := program.ReduceCombinedTree()

		for _, g := range gates {
			fmt.Printf("\n %v", g)
		}

		//fmt.Println("\n generating ER1CS")
		//r1cs := program.GatesToR1CS(gates)
		//fmt.Println(r1cs.L)
		//fmt.Println(r1cs.R)
		//fmt.Println(r1cs.O)

	}

}
