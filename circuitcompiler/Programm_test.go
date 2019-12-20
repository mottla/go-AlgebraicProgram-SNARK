package circuitcompiler

import (
	"fmt"
	bn256 "github.com/mottla/go-AlgebraicProgram-SNARK/circuitcompiler/pairing"
	"github.com/stretchr/testify/assert"
	"math/big"
	"testing"
)

type InOut struct {
	inputs []*big.Int
	result *big.Int
}

type TraceCorrectnessTest struct {
	skipp bool
	code  string
	io    []InOut
}

var bigNumberResult1, _ = new(big.Int).SetString("2297704271284150716235246193843898764109352875", 10)
var bigNumberResult2, _ = new(big.Int).SetString("75263346540254220740876250", 10)

//NOTE that the results are wrong. need to consider that division is now done on a finite field.
//TODO compute new testcases with a python scrypt
var correctnessTest = []TraceCorrectnessTest{
	{skipp: false,
		io: []InOut{{
			inputs: []*big.Int{big.NewInt(int64(3)), big.NewInt(int64(2)), big.NewInt(328329)},
		}},

		code: `
	def main(x,z,w) {
		var k = x*x	
		var arra[]={k,1,2,3}
		k = arra[0]*k
		var l = mul( (k*7)+(3*z) )
		equal(l,w)
		return l*(k*arra[2])
	}

	def mul(a){
		return a*a	
	}
`,
	}, {skipp: true,
		io: []InOut{{
			inputs: []*big.Int{big.NewInt(int64(7)), big.NewInt(int64(11))},
			result: big.NewInt(int64(2160900)),
		}},

		code: `
	def main( x  ,  z ) {
			var res = do(x)+do((3)*z)
			return res*x
		}		

	def do(x){		
		var e = x * 5
		var b = e * e
		var c = b * 7
		var f = c * c
		var d = c + f
		return d
	}`,
	},
	{
		skipp: true,
		io: []InOut{{
			inputs: []*big.Int{big.NewInt(int64(7)), big.NewInt(int64(11))},
			result: big.NewInt(int64(2160900)),
		}},

		code: `
	def main( x  ,  z ) {
		return do(x*1)
	}		

	def do(x){
		var e = x * 5
		var b = e * 6
		var c = b * 7
		var f = c * 1
		var d = c * f
		return d}
	`,
	},
	{
		skipp: true,
		io: []InOut{{
			inputs: []*big.Int{big.NewInt(int64(7)), big.NewInt(int64(11))},
			result: big.NewInt(int64(1729500084900343)),
		}, {
			inputs: []*big.Int{big.NewInt(int64(365235)), big.NewInt(int64(11876525))},

			result: bigNumberResult1,
		}},
		code: `
	def main( x  ,  z ) {
		return do(z) + add(x,x)
	}		

	def do(x){
		var e = x * 5
		var b = e * 6
		var c = b * 7
		var f = c * 1
		var d = c * f
		return d * mul(d,e)
	}
	
	def add(x ,k){
		var z = k * x
		return do(x) + mul(x,z)
	}

	def mul(a,b){
		return a * b
	}`,
	},
}

func TestCorrectness(t *testing.T) {

	for _, test := range correctnessTest {

		if test.skipp {
			continue
		}
		//program := NewProgram(big.NewInt(int64(5)), big.NewInt(int64(5)))
		program := NewProgram(bn256.Order, bn256.Order)
		parser := NewParser(test.code, false)
		circuits := parser.Parse(true)

		fmt.Println("\n unreduced")
		fmt.Println(test.code)

		gates := program.ReduceCombinedTree(circuits)

		for _, g := range gates {
			fmt.Printf("\n %v", g)
		}

		fmt.Println("\n generating ER1CS")
		r1cs := program.GatesToR1CS(gates)
		fmt.Println(r1cs.L)
		fmt.Println(r1cs.R)
		fmt.Println(r1cs.E)
		fmt.Println(r1cs.O)

		for _, io := range test.io {
			inputs := io.inputs
			fmt.Println("input")
			fmt.Println(inputs)
			w, err := r1cs.CalculateWitness(inputs, program.Fields)
			assert.NoError(t, err)
			fmt.Println("witness")
			fmt.Println(w)

		}
	}
}
