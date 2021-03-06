package circuitcompiler

import (
	"fmt"
	//"fmt"
	////"math/big"
	//"strings"
	"testing"
)

var CircuitCorrectnessTest = []string{
	`
func main( a,b,c) {	
	var a[]	= {1,b,3,a}
	var k = a[a[0]*8/8]
	foo(a)
	var d = foo(a)
	return k * b *d
  }
func foo(a){
	return a}
`,
}

func TestPrintTree(t *testing.T) {

	for _, test := range CircuitCorrectnessTest {

		program := Parse(test, true)

		fmt.Println("\n unreduced")
		fmt.Println(test)

		gates := program.Execute()

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
