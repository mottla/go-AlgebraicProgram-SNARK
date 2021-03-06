package circuitcompiler

import (
	"fmt"
	"github.com/mottla/go-AlgebraicProgram-SNARK/testPrograms"
	"github.com/stretchr/testify/assert"
	"testing"
)

func iterate(fromX, toX int, call func(int)) {

	if fromX == toX {

		return
	}
	call(fromX)
	iterate(fromX+1, toX, call)
	return
}
func TestCombineInputs(t *testing.T) {
	ctr := 0
	var ff = func(k int) {
		var EQ = func(i int) {
			ctr++
		}
		iterate(0, 9, EQ)
	}
	iterate(0, 9, ff)
	fmt.Print(ctr)
	return
}

func TestCorrectness(t *testing.T) {

	for _, test := range testPrograms.TestPrograms {
		if test.Skip {
			continue
		}

		fmt.Println("\n unreduced")
		fmt.Println(test.Code)
		program := Parse(test.Code, true)

		gates := program.Execute()

		fmt.Println("\n generating ER1CS")
		r1cs := program.GatesToR1CS(gates, false)
		fmt.Printf("number of gates %v, witness length %v \n ", r1cs.NumberOfGates, r1cs.WitnessLength)
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
			inputs := CombineInputs(program.GetMainCircuit().Inputs, io.Inputs)

			fmt.Println("input")
			fmt.Println(inputs)

			w, err := CalculateWitness(r1cs, inputs)
			assert.NoError(t, err)
			fmt.Printf("witness len %v \n ", len(w))
			fmt.Println(w)
			wSparse, err := CalculateSparseWitness(r1csSparse, inputs)
			assert.NoError(t, err)
			assert.Equal(t, w, wSparse)
			fmt.Println("witness")
			fmt.Println(wSparse)
		}
	}
}
