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
	code string
	io   []InOut
}

var bigNumberResult1, _ = new(big.Int).SetString("2297704271284150716235246193843898764109352875", 10)
var bigNumberResult2, _ = new(big.Int).SetString("75263346540254220740876250", 10)

//NOTE that the results are wrong. need to consider that division is now done on a finite field.
//TODO compute new testcases with a python scrypt
var correctnessTest = []TraceCorrectnessTest{
	{
		io: []InOut{{
			inputs: []*big.Int{big.NewInt(int64(7)), big.NewInt(int64(11))},
			result: big.NewInt(int64(1729500084900343)),
		}, {
			inputs: []*big.Int{big.NewInt(int64(365235)), big.NewInt(int64(11876525))},

			result: bigNumberResult1,
		}},
		code: `
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
	},
	{io: []InOut{{
		inputs: []*big.Int{big.NewInt(int64(7))},
		result: big.NewInt(int64(4)),
	}},
		code: `
	def mul(a,b):
		out = a * b
	
	def main(a):
		b = a * a
		c = 4 - b
		d = 5 * c
		out =  mul(d,c) /  mul(b,b)
	`,
	},
	{io: []InOut{{
		inputs: []*big.Int{big.NewInt(int64(7)), big.NewInt(int64(11))},
		result: big.NewInt(int64(22638)),
	}, {
		inputs: []*big.Int{big.NewInt(int64(365235)), big.NewInt(int64(11876525))},
		result: bigNumberResult2,
	}},
		code: `
	def main(a,b):
		d = b + b
		c = a * d
		e = c - a
		out = e * c
	`,
	},
	{
		io: []InOut{{
			inputs: []*big.Int{big.NewInt(int64(643)), big.NewInt(int64(76548465))},
			result: big.NewInt(int64(98441327276)),
		}, {
			inputs: []*big.Int{big.NewInt(int64(365235)), big.NewInt(int64(11876525))},
			result: big.NewInt(int64(8675445947220)),
		}},
		code: `
	def main(a,b):
		c = a + b
		e = c - a
		f = e + b
		g = f + 2
		out = g * a
	`,
	},
	{
		io: []InOut{{
			inputs: []*big.Int{big.NewInt(int64(3)), big.NewInt(int64(5)), big.NewInt(int64(7)), big.NewInt(int64(11))},
			result: big.NewInt(int64(444675)),
		}},
		code: `
	def main(a,b,c,d):
		e = a * b
		f = c * d
		g = e * f
		h = g / e
		i = h * 5
		out = g * i
	`,
	},
	{
		io: []InOut{{
			inputs: []*big.Int{big.NewInt(int64(3)), big.NewInt(int64(5)), big.NewInt(int64(7)), big.NewInt(int64(11))},
			result: big.NewInt(int64(264)),
		}},
		code: `
	def main(a,b,c,d):
		e = a * 3
		f = b * 7
		g = c * 11
		h = d * 13
		i = e + f
		j = g + h
		k = i + j
		out = k * 1
	`,
	},
}

var correctnessEAPTests = []TraceCorrectnessTest{
	{io: []InOut{{
		inputs: []*big.Int{big.NewInt(int64(7))},
		result: big.NewInt(int64(4)),
	}},
		code: `
	def main(a):
		b = g(a) * a
		c = 4 - b
		d = 5 * c
		out =  d /  b
	`,
	},
	{
		io: []InOut{{
			inputs: []*big.Int{big.NewInt(int64(7)), big.NewInt(int64(11))},
			result: big.NewInt(int64(456533)),
		}},
		code: `
	def main( x  ,  z ) :
		a= foo(z) * z
		b = a * a
		out = a * b

	def foo(x):
		b = x + 7
		out = b * x
	`,
	},
}

func TestCorrectness(t *testing.T) {

	for _, test := range correctnessTest {

		program := NewProgram(bn256.Order, bn256.Order)

		parser := NewParser(test.code, false)
		parser.Parse(program)

		fmt.Println("\n unreduced")
		fmt.Println(test.code)

		gates := program.ReduceCombinedTree()

		for _, g := range gates {
			fmt.Printf("\n %v", g)
		}

		fmt.Println("\n generating ER1CS")
		r1cs := program.GatesToR1CS(gates)
		fmt.Println(r1cs.L)
		fmt.Println(r1cs.R)
		fmt.Println(r1cs.O)

		for _, io := range test.io {
			inputs := io.inputs
			fmt.Println("input")
			fmt.Println(inputs)
			w, err := r1cs.CalculateWitness(inputs, program.Fields)
			assert.NoError(t, err)
			fmt.Println("witness")
			fmt.Println(w)
			assert.Equal(t, io.result, w[len(w)-1])
		}

	}

}

//func TestEAP(t *testing.T) {
//
//	//for i := 0; i < len(correctnessEAPTests);i++ {
//	for i := 0; i < 2; i++ {
//		test := correctnessEAPTests[i]
//		parser := NewParser(strings.NewReader(test.code))
//		program := NewProgram(bn256.Order, bn256.Order)
//		err := parser.Parse(program)
//
//		if err != nil {
//			panic(err)
//		}
//		fmt.Println("\n unreduced")
//		fmt.Println(test.code)
//
//		program.BuildConstraintTrees()
//		for k, v := range program.functions {
//			fmt.Println(k)
//			PrintTree(v.root)
//		}
//
//		fmt.Println("\nReduced gates")
//		//PrintTree(froots["mul"])
//		gates := program.ReduceCombinedTree()
//		for _, g := range gates {
//			fmt.Printf("\n %v", g)
//		}
//
//		fmt.Println("\n generating ER1CS")
//		r1cs := program.GatesToR1CS(gates)
//		fmt.Println(r1cs.L)
//		fmt.Println(r1cs.R)
//		fmt.Println(r1cs.E)
//		fmt.Println(r1cs.O)
//
//		for _, io := range test.io {
//			inputs := io.inputs
//			fmt.Println("input")
//			fmt.Println(inputs)
//			w, err := r1cs.CalculateWitness(inputs, program.Fields)
//			assert.NoError(t, err)
//			fmt.Println("witness")
//			fmt.Println(w)
//			assert.Equal(t, io.result, w[len(w)-1])
//		}
//	}
//}
