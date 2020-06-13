package circuitcompiler

import (
	"fmt"
	"github.com/mottla/go-AlgebraicProgram-SNARK/testPrograms"
	"github.com/stretchr/testify/assert"
	"testing"
)

//NOTE that the results are wrong. need to consider that division is now done on a finite field.
//TODO compute new testcases with a python scrypt

func TestCorrectness(t *testing.T) {

	for _, test := range testPrograms.TestPrograms {

		if test.Skip {
			continue
		}
		//program := newProgram(big.NewInt(int64(5)), big.NewInt(int64(5)))

		program := Parse(test.Code, true)

		fmt.Println("\n unreduced")
		fmt.Println(test.Code)

		gates := program.ReduceCombinedTree()

		//for i, g := range gates {
		//	fmt.Printf("%v %v\n", i, g)
		//}

		fmt.Println("\n generating ER1CS")
		r1cs := program.GatesToR1CS(gates.orderedmGates, false)
		r1csSparse := program.GatesToSparseR1CS(gates.orderedmGates, false)
		fmt.Println(r1cs.L)
		fmt.Println(r1cs.R)
		fmt.Println(r1cs.E)
		fmt.Println(r1cs.O)

		//fmt.Println(r1csSparse.L)
		//fmt.Println(r1csSparse.R)
		//fmt.Println(r1csSparse.E)
		//fmt.Println(r1csSparse.O)
		for _, io := range test.IO {
			fmt.Println("input")
			inputs := CombineInputs(program.GlobalInputs, io.Inputs)
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
