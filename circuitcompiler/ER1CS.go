package circuitcompiler

import (
	"errors"
	"fmt"
	bn256 "github.com/mottla/go-AlgebraicProgram-SNARK/pairing"
	"github.com/mottla/go-AlgebraicProgram-SNARK/utils"
	"math"
	"math/big"
)

var randInput, randOutput = "1@randomIn", "1@randomOut"

type ER1CS struct {
	//indexMap maps each variable to its position in the witness trace
	indexMap                     map[string]uint
	WitnessLength, NumberOfGates int
	//splitMap maps each variable (which is split into its bit represants at some point in the code) onto the positions
	//of the its bits in the indexMap
	splitmap map[string][]uint
	L        [][]*big.Int
	R        [][]*big.Int
	E        [][]*big.Int
	O        [][]*big.Int
}
type ER1CSSparse struct {
	indexMap                     map[string]uint
	splitmap                     map[string][]uint
	WitnessLength, NumberOfGates int
	L                            []*utils.AvlTree
	R                            []*utils.AvlTree
	E                            []*utils.AvlTree
	O                            []*utils.AvlTree
}
type ER1CSsPARSETransposed struct {
	indexMap                     map[string]uint
	WitnessLength, NumberOfGates int
	L                            []*utils.AvlTree
	R                            []*utils.AvlTree
	E                            []*utils.AvlTree
	O                            []*utils.AvlTree
}
type ER1CSTransposed struct {
	indexMap                     map[string]uint
	WitnessLength, NumberOfGates int
	L                            [][]*big.Int
	R                            [][]*big.Int
	E                            [][]*big.Int
	O                            [][]*big.Int
}

func (er1cs *ER1CSSparse) TransposeSparse() (transposed *ER1CSsPARSETransposed) {
	transposed = &ER1CSsPARSETransposed{}
	transposed.indexMap = er1cs.indexMap
	transposed.NumberOfGates = er1cs.NumberOfGates
	transposed.WitnessLength = er1cs.WitnessLength

	transposed.L = utils.TransposeSparse(er1cs.L, er1cs.WitnessLength)
	transposed.R = utils.TransposeSparse(er1cs.R, er1cs.WitnessLength)
	transposed.E = utils.TransposeSparse(er1cs.E, er1cs.WitnessLength)
	transposed.O = utils.TransposeSparse(er1cs.O, er1cs.WitnessLength)

	return
}

func maximum(a ...int) int {
	if len(a) == 0 {
		return math.MinInt64
	}
	return max(a[0], maximum(a[1:]...))

}
func max(a, b int) int {

	if a > b {
		return a
	}
	return b
}

func (er1cs *ER1CS) Transpose() (transposed *ER1CSTransposed) {
	transposed = &ER1CSTransposed{}
	transposed.indexMap = er1cs.indexMap
	transposed.NumberOfGates = er1cs.NumberOfGates
	transposed.WitnessLength = er1cs.WitnessLength
	transposed.L = utils.Transpose(er1cs.L)
	transposed.R = utils.Transpose(er1cs.R)
	transposed.E = utils.Transpose(er1cs.E)
	transposed.O = utils.Transpose(er1cs.O)
	return
}

// R1CSToQAP converts the ER1CS* values to the EAP values
//it uses Lagrange interpolation to to fit a polynomial through each slice. The x coordinate
//is simply a linear increment starting at 1
//within this process, the polynomial is evaluated at position 0
//so an alpha/beta/gamma value is the polynomial evaluated at 0
// the domain polynomial therefor is (-1+x)(-2+x)...(-n+x)
func (er1cs *ER1CSTransposed) ER1CSToEAP() (lPoly, rPoly, ePoly, oPoly [][]*big.Int) {

	lT := er1cs.L
	rT := er1cs.R
	eT := er1cs.E
	oT := er1cs.O
	for i := 0; i < len(lT); i++ {
		lPoly = append(lPoly, utils.Field.PolynomialField.LagrangeInterpolation(lT[i]))

		rPoly = append(rPoly, utils.Field.PolynomialField.LagrangeInterpolation(rT[i]))

		ePoly = append(ePoly, utils.Field.PolynomialField.LagrangeInterpolation(eT[i]))

		oPoly = append(oPoly, utils.Field.PolynomialField.LagrangeInterpolation(oT[i]))
	}
	return
}

// R1CSToQAP converts the ER1CS* values to the EAP values
//it uses Lagrange interpolation to to fit a polynomial through each slice. The x coordinate
//is simply a linear increment starting at 1
//within this process, the polynomial is evaluated at position 0
//so an alpha/beta/gamma value is the polynomial evaluated at 0
// the domain polynomial therefor is (-1+x)(-2+x)...(-n+x)
func (er1cs *ER1CSsPARSETransposed) ER1CSToEAPSparse() (lPoly, rPoly, ePoly, oPoly []*utils.AvlTree) {

	lT := er1cs.L
	rT := er1cs.R
	eT := er1cs.E
	oT := er1cs.O
	for i := 0; i < len(lT); i++ {
		lPoly = append(lPoly, utils.Field.ArithmeticField.InterpolateSparseArray(lT[i], er1cs.WitnessLength))

		rPoly = append(rPoly, utils.Field.ArithmeticField.InterpolateSparseArray(rT[i], er1cs.WitnessLength))

		ePoly = append(ePoly, utils.Field.ArithmeticField.InterpolateSparseArray(eT[i], er1cs.WitnessLength))

		oPoly = append(oPoly, utils.Field.ArithmeticField.InterpolateSparseArray(oT[i], er1cs.WitnessLength))
	}
	return
}

//Calculates the witness (program trace) given some extended rank 1 constraint system
//asserts that ER1CS has been computed and is stored in the program p memory calling this function
func CalculateWitness(r1cs *ER1CS, input []InputArgument) (witness []*big.Int, err error) {

	witness = utils.ArrayOfBigZeros(len(r1cs.indexMap))
	set := make([]bool, len(witness))
	witness[0] = big.NewInt(int64(1))
	set[0] = true

	if r1cs.indexMap[randInput] != 0 {
		rnd, rnderr := utils.Field.ArithmeticField.Rand()
		if rnderr != nil {
			panic(rnderr)
		}
		witness[r1cs.indexMap[randInput]] = rnd
		set[r1cs.indexMap[randInput]] = true
	}

	for _, v := range input {
		witness[r1cs.indexMap[v.identifier]] = v.value
		set[r1cs.indexMap[v.identifier]] = true
	}

	//inverseSplitmap maps each bit index onto (bitposition,positionOfFather)
	inverseSplitmap := make(map[uint][]uint)
	// all inputs, which get split into bits at some point, are now added to the witnesstrace
	for k, v := range r1cs.splitmap {
		if set[r1cs.indexMap[k]] {
			for bitPos, zGateIndex := range v {
				witness[zGateIndex] = big.NewInt(int64(witness[r1cs.indexMap[k]].Bit(bitPos)))
				set[zGateIndex] = true
			}
		}
		for bitpos, zGateIndex := range v {
			inverseSplitmap[zGateIndex] = []uint{uint(bitpos), r1cs.indexMap[k]}
		}

	}

	zero := big.NewInt(int64(0))

	getKnownsAndUnknowns := func(array []*big.Int) (knowns []*big.Int, unknownsAtIndices []int) {
		knowns = utils.ArrayOfBigZeros(len(array))
		for j, val := range array {
			if val.Cmp(zero) != 0 {
				if !set[j] {
					if bitPosAndFather, exists := inverseSplitmap[uint(j)]; exists {
						bit := big.NewInt(int64(witness[bitPosAndFather[1]].Bit(int(bitPosAndFather[0]))))
						witness[j] = bit
						set[j] = true
						knowns[j] = bit
						continue
					}
					unknownsAtIndices = append(unknownsAtIndices, j)
				} else {
					knowns[j] = val
				}
			}
		}
		return
	}

	sum := func(array []*big.Int) *big.Int {
		return field.ScalarProduct(array, witness)
	}

	for i := 0; i < len(r1cs.L); i++ {
		gatesLeftInputs := r1cs.L[i]
		gatesRightInputs := r1cs.R[i]
		gatesExpInputs := r1cs.E[i]
		gatesOutputs := r1cs.O[i]

		leftKnowns, leftUnknowns := getKnownsAndUnknowns(gatesLeftInputs)
		rightKnowns, rightUnknowns := getKnownsAndUnknowns(gatesRightInputs)
		exponentKnowns, exponentUnknowns := getKnownsAndUnknowns(gatesExpInputs)
		if len(exponentUnknowns) > 0 {
			return nil, errors.New(fmt.Sprintf("at gate %v: discret logarithm cannot be computed. if you know how. mail me! please!!", i))
		}
		outKnowns, outUnknowns := getKnownsAndUnknowns(gatesOutputs)

		if len(leftUnknowns)+len(rightUnknowns)+len(outUnknowns) > 1 {
			return nil, errors.New(fmt.Sprintf("at gate %v:computing more then one unknown in Gate assignment is not possible", i))
		}

		// (a*x + b + c..) (d+e+..) + (G^(k+v..)) = (F+g+..)   we solve for x
		if len(leftUnknowns) == 1 {
			sumright := sum(rightKnowns)
			if sumright.Cmp(zero) == 0 {
				fmt.Println(r1cs.L[i])
				fmt.Println(r1cs.R[i])
				fmt.Println(r1cs.E[i])
				fmt.Println(r1cs.O[i])

				return nil, errors.New(fmt.Sprintf("at gate %v:the summation of R inputs cannot be 0 if the unknown is in Lexer", i))
			}
			result := utils.Field.ArithmeticField.Sub(sum(outKnowns), new(bn256.G1).ScalarBaseMult(sum(exponentKnowns)).X())
			result = utils.Field.ArithmeticField.Div(result, sumright)
			result = utils.Field.ArithmeticField.Sub(result, sum(leftKnowns))
			result = utils.Field.ArithmeticField.Div(result, gatesLeftInputs[leftUnknowns[0]]) //divide by a
			set[leftUnknowns[0]] = true
			witness[leftUnknowns[0]] = result
			continue
		}
		// (a + b + c..) (d+e*x+..) + (G^(k+v..)) = (F+g+..)   we solve for x
		if len(rightUnknowns) == 1 {
			sumleft := sum(leftKnowns)
			if sumleft.Cmp(zero) == 0 {
				return nil, errors.New(fmt.Sprintf("at gate %v:the summation of Lexer inputs cannot be 0 if the unknown is in R", i))
			}
			result := utils.Field.ArithmeticField.Sub(sum(outKnowns), new(bn256.G1).ScalarBaseMult(sum(exponentKnowns)).X())
			result = utils.Field.ArithmeticField.Div(result, sumleft)
			result = utils.Field.ArithmeticField.Sub(result, sum(rightKnowns))
			result = utils.Field.ArithmeticField.Div(result, gatesRightInputs[rightUnknowns[0]]) //divide by a
			set[rightUnknowns[0]] = true
			witness[rightUnknowns[0]] = result
			continue
		}

		// (a + b + c..) (d+e+..) + (G^(k+v..)) = (F+x*g+..)   we solve for x
		if len(outUnknowns) == 1 {

			result := utils.Field.ArithmeticField.Mul(sum(rightKnowns), sum(leftKnowns))
			result = utils.Field.ArithmeticField.Add(result, new(bn256.G1).ScalarBaseMult(sum(exponentKnowns)).X())
			result = utils.Field.ArithmeticField.Sub(result, sum(outKnowns))
			result = utils.Field.ArithmeticField.Div(result, gatesOutputs[outUnknowns[0]]) //divide by a
			set[outUnknowns[0]] = true
			witness[outUnknowns[0]] = result
			continue
		}
		//we computed the unkown and now check if the ER1C is satisfied
		leftKnowns, leftUnknowns = getKnownsAndUnknowns(gatesLeftInputs)
		rightKnowns, rightUnknowns = getKnownsAndUnknowns(gatesRightInputs)
		exponentKnowns, exponentUnknowns = getKnownsAndUnknowns(gatesExpInputs)
		outKnowns, outUnknowns = getKnownsAndUnknowns(gatesOutputs)

		if len(leftUnknowns)+len(rightUnknowns)+len(outUnknowns)+len(exponentUnknowns) != 0 {
			return nil, errors.New(fmt.Sprintf("at gate %v some unknowns remain", i))

		}
		//now check if the gate is satisfiable
		result := utils.Field.ArithmeticField.Mul(sum(rightKnowns), sum(leftKnowns))
		result = utils.Field.ArithmeticField.Add(result, new(bn256.G1).ScalarBaseMult(sum(exponentKnowns)).X())
		if result.Cmp(sum(outKnowns)) != 0 {
			return nil, errors.New(fmt.Sprintf("at equality gate %v there is unequality. %v != %v .We cannot process", i, result.String(), sum(outKnowns).String()))
		}

	}

	return
}

//Calculates the witness (program trace) given some extended rank 1 constraint system
//asserts that ER1CS has been computed and is stored in the program p memory calling this function
func CalculateSparseWitness(r1cs *ER1CSSparse, input []InputArgument) (witness []*big.Int, err error) {

	witness = utils.ArrayOfBigZeros(len(r1cs.indexMap))
	set := make([]bool, len(witness))
	witness[0] = big.NewInt(int64(1))
	set[0] = true

	if r1cs.indexMap[randInput] != 0 {
		rnd, rnderr := utils.Field.ArithmeticField.Rand()
		if rnderr != nil {
			panic(rnderr)
		}
		witness[r1cs.indexMap[randInput]] = rnd
		set[r1cs.indexMap[randInput]] = true
	}

	for _, v := range input {
		witness[r1cs.indexMap[v.identifier]] = v.value
		set[r1cs.indexMap[v.identifier]] = true
	}

	//inverseSplitmap maps each bit index onto (bitposition,positionOfFather)
	inverseSplitmap := make(map[uint][]uint)
	// all inputs, which get split into bits at some point, are now added to the witnesstrace
	for k, v := range r1cs.splitmap {
		if set[r1cs.indexMap[k]] {
			for bitPos, zGateIndex := range v {
				witness[zGateIndex] = big.NewInt(int64(witness[r1cs.indexMap[k]].Bit(bitPos)))
				set[zGateIndex] = true
			}
		}
		for bitpos, zGateIndex := range v {
			inverseSplitmap[zGateIndex] = []uint{uint(bitpos), r1cs.indexMap[k]}
		}

	}

	zero := big.NewInt(int64(0))

	getKnownsAndUnknowns := func(array *utils.AvlTree) (knowns *utils.AvlTree, unknownsAtIndices []uint) {
		knowns = utils.NewAvlTree()
		for val := range array.ChannelNodes(true) {
			if !set[val.Key] {
				if bitPosAndFather, exists := inverseSplitmap[val.Key]; exists {
					bit := big.NewInt(int64(witness[bitPosAndFather[1]].Bit(int(bitPosAndFather[0]))))
					witness[val.Key] = bit
					set[val.Key] = true
					knowns.Insert(val.Key, bit)
					continue
				}
				unknownsAtIndices = append(unknownsAtIndices, val.Key)
			} else {
				knowns.Insert(val.Key, val.Value)
			}
		}
		return
	}

	sum := func(array *utils.AvlTree) *big.Int {
		return utils.Field.ArithmeticField.SparseScalarProduct(array, witness)
	}

	for i := 0; i < len(r1cs.L); i++ {
		gatesLeftInputs := r1cs.L[i]
		gatesRightInputs := r1cs.R[i]
		gatesExpInputs := r1cs.E[i]
		gatesOutputs := r1cs.O[i]

		leftKnowns, leftUnknowns := getKnownsAndUnknowns(gatesLeftInputs)
		rightKnowns, rightUnknowns := getKnownsAndUnknowns(gatesRightInputs)
		exponentKnowns, exponentUnknowns := getKnownsAndUnknowns(gatesExpInputs)
		if len(exponentUnknowns) > 0 {
			return nil, errors.New(fmt.Sprintf("at gate %v: discret logarithm cannot be computed. if you know how. mail me! please!!", i))
		}
		outKnowns, outUnknowns := getKnownsAndUnknowns(gatesOutputs)

		if len(leftUnknowns)+len(rightUnknowns)+len(outUnknowns) > 1 {
			return nil, errors.New(fmt.Sprintf("at gate %v:computing more then one unknown in Gate assignment is not possible", i))
		}

		// (a*x + b + c..) (d+e+..) + (G^(k+v..)) = (F+g+..)   we solve for x
		if len(leftUnknowns) == 1 {
			sumright := sum(rightKnowns)
			if sumright.Cmp(zero) == 0 {
				fmt.Println(r1cs.L[i])
				fmt.Println(r1cs.R[i])
				fmt.Println(r1cs.E[i])
				fmt.Println(r1cs.O[i])

				return nil, errors.New(fmt.Sprintf("at gate %v:the summation of R inputs cannot be 0 if the unknown is in Lexer", i))
			}
			result := utils.Field.ArithmeticField.Sub(sum(outKnowns), new(bn256.G1).ScalarBaseMult(sum(exponentKnowns)).X())
			result = utils.Field.ArithmeticField.Div(result, sumright)
			result = utils.Field.ArithmeticField.Sub(result, sum(leftKnowns))
			v, e := gatesLeftInputs.Get(leftUnknowns[0])
			if e != nil {
				return nil, e
			}
			result = utils.Field.ArithmeticField.Div(result, v) //divide by a
			set[leftUnknowns[0]] = true
			witness[leftUnknowns[0]] = result
		}
		// (a + b + c..) (d+e*x+..) + (G^(k+v..)) = (F+g+..)   we solve for x
		if len(rightUnknowns) == 1 {
			sumleft := sum(leftKnowns)
			if sumleft.Cmp(zero) == 0 {
				return nil, errors.New(fmt.Sprintf("at gate %v:the summation of Lexer inputs cannot be 0 if the unknown is in R", i))
			}
			result := utils.Field.ArithmeticField.Sub(sum(outKnowns), new(bn256.G1).ScalarBaseMult(sum(exponentKnowns)).X())
			result = utils.Field.ArithmeticField.Div(result, sumleft)
			result = utils.Field.ArithmeticField.Sub(result, sum(rightKnowns))
			v, e := gatesRightInputs.Get(rightUnknowns[0])
			if e != nil {
				return nil, e
			}
			result = utils.Field.ArithmeticField.Div(result, v) //divide by a
			set[rightUnknowns[0]] = true
			witness[rightUnknowns[0]] = result
		}

		// (a + b + c..) (d+e+..) + (G^(k+v..)) = (F+x*g+..)   we solve for x
		if len(outUnknowns) == 1 {

			result := utils.Field.ArithmeticField.Mul(sum(rightKnowns), sum(leftKnowns))
			result = utils.Field.ArithmeticField.Add(result, new(bn256.G1).ScalarBaseMult(sum(exponentKnowns)).X())
			result = utils.Field.ArithmeticField.Sub(result, sum(outKnowns))
			v, e := gatesOutputs.Get(outUnknowns[0])
			if e != nil {
				return nil, e
			}
			result = utils.Field.ArithmeticField.Div(result, v) //divide by a
			set[outUnknowns[0]] = true
			witness[outUnknowns[0]] = result
		}

		//we computed the unkown and now check if the ER1C is satisfied
		leftKnowns, leftUnknowns = getKnownsAndUnknowns(gatesLeftInputs)
		rightKnowns, rightUnknowns = getKnownsAndUnknowns(gatesRightInputs)
		exponentKnowns, exponentUnknowns = getKnownsAndUnknowns(gatesExpInputs)
		outKnowns, outUnknowns = getKnownsAndUnknowns(gatesOutputs)

		if len(leftUnknowns)+len(rightUnknowns)+len(outUnknowns)+len(exponentUnknowns) != 0 {
			return nil, errors.New(fmt.Sprintf("at gate %v some unknowns remain", i))

		}
		//now check if the gate is satisfiable
		result := utils.Field.ArithmeticField.Mul(sum(rightKnowns), sum(leftKnowns))
		result = utils.Field.ArithmeticField.Add(result, new(bn256.G1).ScalarBaseMult(sum(exponentKnowns)).X())
		if result.Cmp(sum(outKnowns)) != 0 {
			return nil, errors.New(fmt.Sprintf("at equality gate %v there is unequality. %v != %v .We cannot process", i, result.String(), sum(outKnowns).String()))
		}

	}

	return
}
