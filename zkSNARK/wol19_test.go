package zkSNARK

import (
	"fmt"
	"github.com/mottla/go-AlgebraicProgram-SNARK/circuitcompiler"
	bn256 "github.com/mottla/go-AlgebraicProgram-SNARK/circuitcompiler/pairing"
	"github.com/stretchr/testify/assert"
	"math/big"
	"testing"
	"time"
)

type InOut struct {
	inputs []*big.Int
	result *big.Int
}

type TraceCorrectnessTest struct {
	code  string
	io    []InOut
	skipp bool
}

var bigNumberResult1, _ = new(big.Int).SetString("2297704271284150716235246193843898764109352875", 10)
var correctnessEAPTests = []TraceCorrectnessTest{

	{
		skipp: false,
		io: []InOut{{
			inputs: []*big.Int{big.NewInt(int64(7)), big.NewInt(int64(11))},
			result: big.NewInt(int64(1729500084900343)),
		}, {
			inputs: []*big.Int{big.NewInt(int64(365235)), big.NewInt(int64(11876525))},

			result: bigNumberResult1,
		}},
		code: `
	def main( x  ,  z ) {
		return (do(z) + add(x,x))*x
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

func TestGenerateAndVerifyProof(t *testing.T) {

	for _, test := range correctnessEAPTests {
		if test.skipp {
			continue
		}
		program := circuitcompiler.NewProgram(bn256.Order, bn256.Order)
		parser := circuitcompiler.NewParser(test.code, false)
		circuits := parser.Parse(true)

		fmt.Println("\n unreduced")
		fmt.Println(test.code)

		gates := program.ReduceCombinedTree(circuits)
		program.Fields.PolynomialField.InitBases(len(gates))
		for _, g := range gates {
			fmt.Printf("\n %v", g)
		}

		fmt.Println("\n generating ER1CS")
		r1cs := program.GatesToR1CS(gates)
		trasposedR1Cs := r1cs.Transpose()
		fmt.Println(r1cs.L)
		fmt.Println(r1cs.R)
		fmt.Println(r1cs.E)
		fmt.Println(r1cs.O)
		// ER1CS to QAP
		l, r, e, o := trasposedR1Cs.ER1CSToEAP(program.Fields)
		//fmt.Println(l)
		//fmt.Println(r)
		//fmt.Println(e)
		//fmt.Println(o)

		setup, err := GenerateTrustedSetup(program.Fields, len(r1cs.L[0]), len(r1cs.L), 2, l, r, e, o)
		assert.NoError(t, err)

		for _, io := range test.io {
			inputs := io.inputs
			w, err := r1cs.CalculateWitness(inputs, program.Fields)
			assert.NoError(t, err)
			fmt.Println("input")
			fmt.Println(inputs)
			fmt.Println("witness")
			fmt.Println(w)
			//assert.Equal(t, io.result, w[len(w)-1])

			mf, px := CombinePolynomials2(program.Fields, w, trasposedR1Cs)
			_, px2 := CombinePolynomials(program.Fields, w, l, r, e, o)
			assert.Equal(t, px, px2)

			var bigZero = big.NewInt(int64(0))

			//Test if P(x) is indeed 0 at each gate index
			for i := 0; i < len(gates); i++ {
				if bigZero.Cmp(program.Fields.ArithmeticField.EvalPoly(px, new(big.Int).SetInt64(int64(i)))) != 0 {
					t.Error("Px must be zero ate each gate")
				}
			}
			//assert.Equal(t, Utils.PolynomialField.Mul(l,r)
			Qx, _ := program.Fields.PolynomialField.Div(px, setup.Pk.Domain)
			pf := program.Fields.PolynomialField
			LVec := pf.AddPolynomials(pf.LinearCombine(l, w))
			RVec := pf.AddPolynomials(pf.LinearCombine(r, w))
			//EVec := pf.AddPolynomials(pf.LinearCombine(Ei, witness))
			OVec := pf.AddPolynomials(pf.LinearCombine(o, w))

			assert.Equal(t, pf.Add(pf.Mul(LVec, RVec), mf), pf.Add(OVec, pf.Mul(Qx, setup.Pk.Domain)))

			before := time.Now()
			proof, err := GenerateProofs(program.Fields, len(r1cs.L[0]), 2, &setup.Pk, w, px)
			{
				x, _ := program.Fields.CurveOrderField.Rand()

				assert.Equal(t, g1ScalarBaseMultiply(x), new(bn256.G1).Add(g1ScalarBaseMultiply(x), g1ScalarBaseMultiply(big.NewInt(0))))

				assert.Equal(t, g1ScalarBaseMultiply(x), new(bn256.G1).ScalarMult(g1ScalarBaseMultiply(big.NewInt(1)), x))

				ter := new(big.Int).Set(x)
				icPubl := new(bn256.G1).ScalarMult(g1ScalarBaseMultiply(big.NewInt(1)), px[0])

				for i := 1; i < len(px); i++ {
					icPubl.Add(icPubl, new(bn256.G1).ScalarMult(g1ScalarBaseMultiply(ter), px[i]))
					ter = program.Fields.CurveOrderField.Mul(ter, x)
				}

				assert.Equal(t, icPubl.String(), g1ScalarBaseMultiply(program.Fields.CurveOrderField.EvalPoly(px, x)).String())

			}

			fmt.Println("proof generation time elapsed:", time.Since(before))
			assert.Nil(t, err)

			before = time.Now()

			assert.True(t, VerifyProof(&setup.Pk, proof, w[:3], true))
			fmt.Println("verify proof time elapsed:", time.Since(before))
		}

	}

}
