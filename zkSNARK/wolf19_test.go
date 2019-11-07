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
	{
		io: []InOut{{
			inputs: []*big.Int{big.NewInt(int64(7)), big.NewInt(int64(11))},
			result: big.NewInt(int64(456533)),
		}},
		code: `
	def main( x  ,  z ) :
		a= x * z
		b = a * a
		out = a * b
	`,
	},
}

func TestGenerateAndVerifyProof(t *testing.T) {

	for _, test := range correctnessEAPTests {
		parser := circuitcompiler.NewParser(strings.NewReader(test.code))
		program := circuitcompiler.NewProgram(bn256.P)
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
		program.Fields.PF.InitBases(len(gates))
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
		fmt.Println(trasposedR1Cs.L)
		fmt.Println(trasposedR1Cs.R)
		fmt.Println(trasposedR1Cs.E)
		fmt.Println(trasposedR1Cs.O)
		// ER1CS to QAP
		l, r, e, o := trasposedR1Cs.ER1CSToEAP(program.Fields)
		fmt.Println(l)
		fmt.Println(r)
		fmt.Println(e)
		fmt.Println(o)
		setup, err := GenerateTrustedSetup(program.Fields, len(r1cs.L[0]), len(r1cs.L), 2, l, r, e, o)

		for _, io := range test.io {
			inputs := io.inputs
			w := r1cs.CalculateWitness(inputs, program.Fields)

			fmt.Println("input")
			fmt.Println(inputs)
			fmt.Println("witness")
			fmt.Println(w)
			assert.Equal(t, io.result, w[len(w)-1])

			_, px := CombinePolynomials2(program.Fields, w, trasposedR1Cs)
			_, px2 := CombinePolynomials(program.Fields, w, l, r, e, o)
			assert.Equal(t, px, px2)

			var bigZero = big.NewInt(int64(0))
			for i := 0; i < len(gates); i++ {
				if bigZero.Cmp(program.Fields.PF.Eval(px, new(big.Int).SetInt64(int64(i)))) != 0 {
					t.Error("Px must be zero ate each gate")
				}
			}
			//assert.Equal(t, Utils.PF.Mul(l,r)
			Qx, _ := program.Fields.PF.Div(px, setup.Pk.Domain)
			pf := program.Fields.PF
			LVec := pf.AddPolynomials(pf.LinearCombine(l, w))
			RVec := pf.AddPolynomials(pf.LinearCombine(r, w))
			//EVec := pf.AddPolynomials(pf.LinearCombine(Ei, witness))
			OVec := pf.AddPolynomials(pf.LinearCombine(o, w))
			//only when E is not used
			assert.Equal(t, pf.Mul(LVec, RVec), pf.Add(OVec, pf.Mul(Qx, setup.Pk.Domain)))

			before := time.Now()
			proof, err := GenerateProofs(program.Fields, len(r1cs.L[0]), 2, &setup.Pk, w, px)

			fmt.Println("proof generation time elapsed:", time.Since(before))
			assert.Nil(t, err)

			before = time.Now()

			assert.True(t, VerifyProof(&setup.Pk, proof, w[:3], true))
			fmt.Println("verify proof time elapsed:", time.Since(before))
		}

	}

}
