package circuitcompiler

import (
	"fmt"
	"github.com/mottla/go-AlgebraicProgram-SNARK/testPrograms"
	"github.com/stretchr/testify/assert"
	"testing"
)

func TestCorrectness(t *testing.T) {

	for _, test := range testPrograms.TestPrograms {
		if test.Skip {
			continue
		}

		program := Parse(test.Code, true)

		fmt.Println("\n unreduced")
		fmt.Println(test.Code)

		gates := program.Execute()

		fmt.Println("\n generating ER1CS")
		r1cs := program.GatesToR1CS(gates, false)
		r1csSparse := program.GatesToSparseR1CS(gates, false)
		fmt.Println(r1cs.L)
		fmt.Println(r1cs.R)
		fmt.Println(r1cs.E)
		fmt.Println(r1cs.O)

		//fmt.Println(r1csSparse.L)
		//fmt.Println(r1csSparse.R)
		//fmt.Println(r1csSparse.E)
		//fmt.Println(r1csSparse.O)
		for _, io := range test.IO {
			inputs := CombineInputs(program.GlobalInputs, io.Inputs)

			fmt.Println("input")
			fmt.Println(inputs)

			w, err := CalculateWitness(r1cs, inputs)
			assert.NoError(t, err)
			fmt.Println("witness")
			fmt.Println(w)
			wSparse, err := CalculateSparseWitness(r1csSparse, inputs)
			assert.NoError(t, err)
			assert.Equal(t, w, wSparse)
			fmt.Println("witness")
			fmt.Println(wSparse)
		}
	}
}
