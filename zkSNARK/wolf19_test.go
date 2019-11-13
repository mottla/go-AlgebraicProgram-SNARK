package zkSNARK

import (
	"fmt"
	"github.com/mottla/go-AlgebraicProgram-SNARK/circuitcompiler"
	bn256 "github.com/mottla/go-AlgebraicProgram-SNARK/circuitcompiler/pairing"
	"github.com/stretchr/testify/assert"
	"math/big"
	"strings"
	"testing"
	"time"
)

type InOut struct {
	inputs []*big.Int
	result *big.Int
}

type TraceCorrectnessTest struct {
	code string
	io   []InOut
}

var correctnessEAPTests = []TraceCorrectnessTest{
	//{
	//	io: []InOut{{
	//		inputs: []*big.Int{big.NewInt(int64(7)), big.NewInt(int64(11))},
	//		result: big.NewInt(int64(456533)),
	//	}},
	//	code: `
	//def main( x  ,  z ) :
	//	a= x * z
	//	b = a * a
	//	out = a * b
	//`,
	//},
	{
		io: []InOut{{
			inputs: []*big.Int{big.NewInt(int64(7)), big.NewInt(int64(3))},
			result: big.NewInt(int64(1764)),
		}},
		code: `
	def foo(x):
		out = x * x

	def main( x  ,  z ) :		
		b = g(z) * 1
		c = b + x		
		out = c * b 
	`,
	},
}

func TestGenerateAndVerifyProof(t *testing.T) {

	for _, test := range correctnessEAPTests {
		parser := circuitcompiler.NewParser(strings.NewReader(test.code))
		//TODO fix that arithmetic circuit can have different field order
		program := circuitcompiler.NewProgram(bn256.Order, bn256.Order)
		err := parser.Parse(program)

		if err != nil {
			panic(err)
		}
		fmt.Println("\n unreduced")
		fmt.Println(test.code)

		program.BuildConstraintTrees()

		program.PrintContraintTrees()

		fmt.Println("\nReduced gates")
		//PrintTree(froots["mul"])
		gates := program.ReduceCombinedTree()
		program.Fields.PolynomialField.InitBases(len(gates))
		for _, g := range gates {
			fmt.Printf("\n %v", g)
		}

		fmt.Println("\n generating ER1CS")
		r1cs := program.GenerateReducedR1CS(gates)
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

//remove soon
func TestGroupOrderModulo(t *testing.T) {
	f := circuitcompiler.PrepareFields(bn256.Order, bn256.P)
	for i := 1; i < 100; i++ {
		x, _ := f.ArithmeticField.Rand()
		assert.Equal(t, g1ScalarBaseMultiply(x), g1ScalarBaseMultiply(new(big.Int).Mod(x, bn256.Order)))
	}

}

func TestBlindEvaluation(t *testing.T) {
	{
		f := circuitcompiler.PrepareFields(bn256.Order, bn256.P)
		//px := []*big.Int{big.NewInt(1), big.NewInt(2), big.NewInt(3), big.NewInt(4), big.NewInt(5)}
		NPoints := int64(10)
		FakePoly := make([]*big.Int, NPoints)
		var err error
		for i := int64(0); i < NPoints; i++ {
			FakePoly[i], err = f.ArithmeticField.Rand()
			assert.Nil(t, err)
		}

		x, _ := f.CurveOrderField.Rand()

		assert.Equal(t, g1ScalarBaseMultiply(x), new(bn256.G1).Add(g1ScalarBaseMultiply(x), g1ScalarBaseMultiply(big.NewInt(0))))

		assert.Equal(t, g1ScalarBaseMultiply(x), new(bn256.G1).ScalarMult(g1ScalarBaseMultiply(big.NewInt(1)), x))

		ter := new(big.Int).Set(x)
		icPubl := new(bn256.G1).ScalarMult(g1ScalarBaseMultiply(big.NewInt(1)), FakePoly[0])

		//fmt.Println(g1ScalarBaseMultiply(big.NewInt(1)).String())
		for i := 1; i < len(FakePoly); i++ {
			//fmt.Println(i)
			//fmt.Println(ter.String())
			//fmt.Println(g1ScalarBaseMultiply(f.CurveOrderField.Mul(ter, FakePoly[i])).String())
			//fmt.Println(new(bn256.G1).ScalarMult(g1ScalarBaseMultiply(ter), FakePoly[i]).String())

			assert.Equal(t, g1ScalarBaseMultiply(f.CurveOrderField.Mul(ter, FakePoly[i])).String(), new(bn256.G1).ScalarMult(g1ScalarBaseMultiply(ter), FakePoly[i]).String())

			icPubl.Add(icPubl, new(bn256.G1).ScalarMult(g1ScalarBaseMultiply(ter), FakePoly[i]))
			ter = f.CurveOrderField.Mul(ter, x)
		}

		//if !bytes.Equal(icPubl.Marshal(), g1ScalarBaseMultiply(pf.Eval(px, x)).Marshal()) {
		//	panic("ARTIFICIAL FAILED")
		//}
		assert.Equal(t, icPubl.String(), g1ScalarBaseMultiply(f.CurveOrderField.EvalPoly(FakePoly, x)).String())

	}
}
