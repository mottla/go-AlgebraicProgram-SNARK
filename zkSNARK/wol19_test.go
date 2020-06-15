package zkSNARK

import (
	"fmt"
	"github.com/mottla/go-AlgebraicProgram-SNARK/circuitcompiler"
	bn256 "github.com/mottla/go-AlgebraicProgram-SNARK/pairing"
	"github.com/mottla/go-AlgebraicProgram-SNARK/testPrograms"
	"github.com/mottla/go-AlgebraicProgram-SNARK/utils"
	"github.com/stretchr/testify/assert"
	"math/big"
	"testing"
	"time"
)

func TestGenerateAndVerifyProof_OldArray(t *testing.T) {

	for _, test := range testPrograms.TestPrograms {
		if test.Skip {
			continue
		}

		program := circuitcompiler.Parse(test.Code, true)

		fmt.Println("Code>>")
		fmt.Println(test.Code)

		before := time.Now()
		fmt.Println("Generating CRS...")
		gates := program.Execute()
		utils.Field.PolynomialField.InitBases(len(gates) + 1)

		fmt.Println("\n generating ER1CS")
		r1cs := program.GatesToR1CS(gates, true)

		//r1csSparse := program.GatesToSparseR1CS(gates, true)
		//transposedR1csSparse := r1csSparse.TransposeSparse()
		trasposedR1Cs := r1cs.Transpose()
		//fmt.Println(r1cs.L)
		//fmt.Println(r1cs.R)
		//fmt.Println(r1cs.E)
		//fmt.Println(r1cs.O)
		// ER1CS to QAP
		l, r, e, o := trasposedR1Cs.ER1CSToEAP()
		//fmt.Println(l)
		//fmt.Println(r)
		//fmt.Println(e)
		//fmt.Println(o)

		setup, err := GenerateTrustedSetup(program.GlobalInputCount(), l, r, e, o)
		fmt.Println("CRS generation time elapsed:", time.Since(before))
		assert.NoError(t, err)

		for _, io := range test.IO {
			inputs := circuitcompiler.CombineInputs(program.GlobalInputs, io.Inputs)
			w, err := circuitcompiler.CalculateWitness(r1cs, inputs)

			assert.NoError(t, err)
			//wsparse, werr := circuitcompiler.CalculateSparseWitness(r1csSparse, inputs)
			//assert.NoError(t, werr)

			fmt.Println("input")
			fmt.Println(inputs)
			fmt.Println("witness")
			fmt.Println(w)
			//fmt.Println(wsparse)
			//assert.Equal(t, io.result, w[len(w)-1])
			// CombineSparsePolynomials(program.Fields, w, transposedR1csSparse)
			mf, px := CombinePolynomials2(w, trasposedR1Cs)
			//mf3,px3 := CombinePolynomials3(program.Fields,w,trasposedR1Cs)
			//mSparse,pSparse := CombineSparsePolynomials(program.Fields,wSparse,r1csSparse)
			mf2, px2 := CombinePolynomials(w, l, r, e, o)
			assert.Equal(t, px, px2)
			assert.Equal(t, mf2, mf)
			//assert.Equal(t, px, px3)
			//assert.Equal(t, mf2, mf3)
			var bigZero = big.NewInt(int64(0))

			//Test if P(x) is indeed 0 at each gate index
			for i := 0; i < len(gates); i++ {
				if bigZero.Cmp(utils.Field.ArithmeticField.EvalPoly(px, new(big.Int).SetInt64(int64(i)))) != 0 {
					t.Error("Px must be zero ate each gate")
				}
			}
			//assert.Equal(t, Utils.PolynomialField.Mul(l,r)
			Qx, _ := utils.Field.PolynomialField.Div(px, setup.Pk.Domain)
			pf := utils.Field.PolynomialField
			LVec := pf.AddPolynomials(pf.LinearCombine(l, w))
			RVec := pf.AddPolynomials(pf.LinearCombine(r, w))
			//EVec := pf.AddPolynomials(pf.LinearCombine(Ei, witness))
			OVec := pf.AddPolynomials(pf.LinearCombine(o, w))

			assert.Equal(t, pf.Add(pf.Mul(LVec, RVec), mf), pf.Add(OVec, pf.Mul(Qx, setup.Pk.Domain)))

			before := time.Now()
			proof, err := GenerateProofs(program.GlobalInputCount(), &setup.Pk, w, px)
			{
				x, _ := utils.Field.CurveOrderField.Rand()

				assert.Equal(t, g1ScalarBaseMultiply(x), new(bn256.G1).Add(g1ScalarBaseMultiply(x), g1ScalarBaseMultiply(big.NewInt(0))))
				assert.Equal(t, g1ScalarBaseMultiply(x), new(bn256.G1).ScalarMult(g1ScalarBaseMultiply(big.NewInt(1)), x))

				ter := new(big.Int).Set(x)
				icPubl := new(bn256.G1).ScalarMult(g1ScalarBaseMultiply(big.NewInt(1)), px[0])

				for i := 1; i < len(px); i++ {
					icPubl.Add(icPubl, new(bn256.G1).ScalarMult(g1ScalarBaseMultiply(ter), px[i]))
					ter = utils.Field.CurveOrderField.Mul(ter, x)
				}

				assert.Equal(t, icPubl.String(), g1ScalarBaseMultiply(utils.Field.CurveOrderField.EvalPoly(px, x)).String())

			}
			fmt.Println("proof generation time elapsed:", time.Since(before))
			assert.Nil(t, err)
			before = time.Now()
			assert.True(t, VerifyProof(&setup.Pk, proof, w[:program.GlobalInputCount()], true))
			fmt.Println("verify proof time elapsed:", time.Since(before))
			fmt.Println("Proof Elements: ", proof)
		}

	}

}
