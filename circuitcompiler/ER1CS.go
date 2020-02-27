package circuitcompiler

import (
	"errors"
	"fmt"
	"github.com/go-ethereum/common/math"
	bn256 "github.com/mottla/go-AlgebraicProgram-SNARK/pairing"
	"github.com/mottla/go-AlgebraicProgram-SNARK/utils"
	"math/big"
)

var randInput, randOutput = "1@randomIn", "1@randomOut"

type ER1CS struct {
	indexMap map[string]int
	L        [][]*big.Int
	R        [][]*big.Int
	E        [][]*big.Int
	O        [][]*big.Int
}
type ER1CSSparse struct {
	indexMap map[string]int
	L        []*utils.AvlTree
	R        []*utils.AvlTree
	E        []*utils.AvlTree
	O        []*utils.AvlTree
}
type ER1CSsPARSETransposed struct {
	indexMap map[string]int
	MaxKey   int
	L        []*utils.AvlTree
	R        []*utils.AvlTree
	E        []*utils.AvlTree
	O        []*utils.AvlTree
}
type ER1CSTransposed struct {
	indexMap map[string]int
	L        [][]*big.Int
	R        [][]*big.Int
	E        [][]*big.Int
	O        [][]*big.Int
}

func (er1cs *ER1CSSparse) TransposeSparse() (transposed ER1CSsPARSETransposed) {
	transposed.indexMap = er1cs.indexMap
	var l, r, e, o int
	transposed.L, l = utils.TransposeSparse(er1cs.L)
	transposed.R, r = utils.TransposeSparse(er1cs.R)
	transposed.E, e = utils.TransposeSparse(er1cs.E)
	transposed.O, o = utils.TransposeSparse(er1cs.O)
	transposed.MaxKey = maximum(l, r, e, o)
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

func (er1cs *ER1CS) Transpose() (transposed ER1CSTransposed) {
	transposed.indexMap = er1cs.indexMap
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

//Calculates the witness (program trace) given some extended rank 1 constraint system
//asserts that ER1CS has been computed and is stored in the program p memory calling this function
func CalculateWitness(r1cs *ER1CS, input []InputArgument) (witness []*big.Int, err error) {

	witness = utils.ArrayOfBigZeros(len(r1cs.indexMap))
	set := make([]bool, len(witness))
	witness[0] = big.NewInt(int64(1))
	rnd, rnderr := utils.Field.CurveOrderField.Rand()
	if rnderr != nil {
		panic(rnderr)
	}
	witness[r1cs.indexMap[randInput]] = rnd
	set[0] = true
	set[r1cs.indexMap[randInput]] = true
	for _, v := range input {
		witness[r1cs.indexMap[v.identifier]] = v.value
		set[r1cs.indexMap[v.identifier]] = true
	}

	zero := big.NewInt(int64(0))

	getKnownsAndUnknowns := func(array []*big.Int) (knowns []*big.Int, unknownsAtIndices []int) {
		knowns = utils.ArrayOfBigZeros(len(array))
		for j, val := range array {
			if val.Cmp(zero) != 0 {
				if !set[j] {
					unknownsAtIndices = append(unknownsAtIndices, j)
				} else {
					knowns[j] = val
				}
			}
		}
		return
	}

	sum := func(array []*big.Int) *big.Int {
		return utils.Field.ArithmeticField.ScalarProduct(array, witness)
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

		//equality gate
		if len(leftUnknowns)+len(rightUnknowns)+len(outUnknowns) == 0 {
			result := utils.Field.ArithmeticField.Mul(sum(rightKnowns), sum(leftKnowns))
			if result.Cmp(sum(outKnowns)) != 0 {
				return nil, errors.New(fmt.Sprintf("at equality gate %v there is unequality. %v != %v .We cannot process", i, result.String(), sum(outKnowns).String()))
			}

		}

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

	}

	return
}

//Calculates the witness (program trace) given some extended rank 1 constraint system
//asserts that ER1CS has been computed and is stored in the program p memory calling this function
func CalculateSparseWitness(r1cs *ER1CSSparse, input []InputArgument) (witness []*big.Int, err error) {

	witness = utils.ArrayOfBigZeros(len(r1cs.indexMap))
	set := make([]bool, len(witness))
	witness[0] = big.NewInt(int64(1))
	rnd, rnderr := utils.Field.CurveOrderField.Rand()
	if rnderr != nil {
		panic(rnderr)
	}
	witness[r1cs.indexMap[randInput]] = rnd
	set[0] = true
	set[r1cs.indexMap[randInput]] = true
	for _, v := range input {
		witness[r1cs.indexMap[v.identifier]] = v.value
		set[r1cs.indexMap[v.identifier]] = true
	}

	zero := big.NewInt(int64(0))

	getKnownsAndUnknowns := func(array *utils.AvlTree) (knowns *utils.AvlTree, unknownsAtIndices []uint) {
		knowns = utils.NewAvlTree()
		for val := range array.ChannelNodes(true) {
			if !set[val.Key] {
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

		//equality gate
		if len(leftUnknowns)+len(rightUnknowns)+len(outUnknowns) == 0 {
			result := utils.Field.ArithmeticField.Mul(sum(rightKnowns), sum(leftKnowns))
			if result.Cmp(sum(outKnowns)) != 0 {
				return nil, errors.New(fmt.Sprintf("at equality gate %v there is unequality. %v != %v .We cannot process", i, result.String(), sum(outKnowns).String()))
			}

		}

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
			v, e := gatesRightInputs.Get(rightUnknowns[0])
			if e != nil {
				return nil, e
			}
			result = utils.Field.ArithmeticField.Div(result, v) //divide by a
			set[rightUnknowns[0]] = true
			witness[rightUnknowns[0]] = result
			continue
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
			continue
		}

	}

	return
}
