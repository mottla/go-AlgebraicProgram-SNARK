package circuitcompiler

import (
	"fmt"
	"github.com/stretchr/testify/assert"
	"strings"
	"testing"
	"time"
)

func TestGenerateAndVerifyProof(t *testing.T) {

	for _, test := range correctnessEAPTests {
		parser := NewParser(strings.NewReader(test.code))
		program := NewProgram()
		err := parser.Parse(program)

		if err != nil {
			panic(err)
		}
		fmt.Println("\n unreduced")
		fmt.Println(test.code)

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

		fmt.Println("\n generating R1CS")
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
		// R1CS to QAP
		l, r, e, o, _ := Utils.PF.ER1CSToEAP(trasposedR1Cs)
		setup, err := GenerateTrustedSetup(len(r1cs.L[0]), len(r1cs.L), 2, l, r, e, o)
		fmt.Println(l)
		fmt.Println(r)
		fmt.Println(e)
		fmt.Println(o)
		for _, io := range test.io {
			inputs := io.inputs
			w := CalculateWitness(inputs, r1cs)

			fmt.Println("input")
			fmt.Println(inputs)
			fmt.Println("witness")
			fmt.Println(w)
			assert.Equal(t, io.result, w[len(w)-1])

			_, px := CombinePolynomials(w, trasposedR1Cs)
			fmt.Println("Px Polynomial")
			fmt.Println(px)

			//assert.Equal(t, Utils.PF.Mul(l,r)

			before := time.Now()
			proof, err := GenerateProofs(len(r1cs.L[0]), 2, setup.Pk, w, px)

			fmt.Println("proof generation time elapsed:", time.Since(before))
			assert.Nil(t, err)

			before = time.Now()

			assert.True(t, VerifyProof(setup.Pk, proof, w[:3], true))
			fmt.Println("verify proof time elapsed:", time.Since(before))
		}

	}

}
