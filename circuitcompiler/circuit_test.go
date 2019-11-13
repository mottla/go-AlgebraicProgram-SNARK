package circuitcompiler

import (
	"fmt"
	bn256 "github.com/mottla/go-AlgebraicProgram-SNARK/circuitcompiler/pairing"
	"strings"

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
	def main( x  ,  z ) :
		out = do(z) + add(x,x)

	def do(x):
		e = x * 5
		b = e * 6
		c = b * 7
		f = c * 1
		d = c * f
		out = d * mul(d,e)
	
	def add(x ,k):
		z = k * x
		out = do(x) + mul(x,z)
	

	def mul(a,b):
		out = a * b
	`,
}

func TestParser_Parse(t *testing.T) {
	for _, code := range CircuitCorrectnessTest {
		parser := NewParser(strings.NewReader(code))
		program := NewProgram(bn256.Order, bn256.Order)
		err := parser.Parse(program)

		if err != nil {
			panic(err)
		}
		fmt.Println("\n unreduced")
		fmt.Println(code)

		program.BuildConstraintTrees()
		for k, v := range program.functions {
			fmt.Println(k)
			PrintTree(v.root)
		}

		fmt.Println("\nReduced gates")
		//PrintTree(froots["mul"])
		gates := program.ReduceCombinedTree()
		for _, g := range gates {
			fmt.Printf("\n %v", g)
		}
	}

}
