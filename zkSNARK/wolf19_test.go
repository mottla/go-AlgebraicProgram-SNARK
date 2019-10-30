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
		program := circuitcompiler.NewProgram(bn256.Order)
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
		l, r, e, o, _ := r1cs.ER1CSToEAP(program.Fields)
		setup, err := GenerateTrustedSetup(program.Fields, len(r1cs.L[0]), len(r1cs.L), 2, l, r, e, o)
		fmt.Println(l)
		fmt.Println(r)
		fmt.Println(e)
		fmt.Println(o)
		for _, io := range test.io {
			inputs := io.inputs
			w := r1cs.CalculateWitness(inputs, program.Fields)

			fmt.Println("input")
			fmt.Println(inputs)
			fmt.Println("witness")
			fmt.Println(w)
			assert.Equal(t, io.result, w[len(w)-1])

			_, px := CombinePolynomials(program.Fields, w, trasposedR1Cs)
			fmt.Println("Px Polynomial")
			fmt.Println(px)

			//assert.Equal(t, Utils.PF.Mul(l,r)

			before := time.Now()
			proof, err := GenerateProofs(program.Fields, len(r1cs.L[0]), 2, setup.Pk, w, px)

			fmt.Println("proof generation time elapsed:", time.Since(before))
			assert.Nil(t, err)

			before = time.Now()

			assert.True(t, VerifyProof(setup.Pk, proof, w[:3], true))
			fmt.Println("verify proof time elapsed:", time.Since(before))
		}

	}

}
