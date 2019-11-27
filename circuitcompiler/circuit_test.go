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
	//3 gates needed. nice dude
	//	`
	//def foo(a){
	//return a*a
	//}
	//	def main( x ) {
	//		return foo(x)*foo(x*x)
	//		}`,

	`
def main( a,b,c) {
	var d = 2
	var a[]	= {1,b,3,a}
	var k = a[1*1]*a[d/2]*b
	return k * b *b
  }`,
}

func TestPrintTree(t *testing.T) {

	for _, test := range CircuitCorrectnessTest {

		program := NewProgram(bn256.Order, bn256.Order)

		parser := NewParser(test, false)
		fkts := parser.Parse(true)

		fmt.Println("\n unreduced")
		fmt.Println(test)

		gates := program.ReduceCombinedTree(fkts)

		for _, g := range gates {
			fmt.Printf("\n %v", g)
		}

		//fmt.Println("\n generating ER1CS")
		//r1cs := program.GatesToR1CS(gates)
		//fmt.Println(r1cs.Lexer)
		//fmt.Println(r1cs.R)
		//fmt.Println(r1cs.O)

	}

}
