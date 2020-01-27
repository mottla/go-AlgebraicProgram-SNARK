package circuitcompiler

import (
	"errors"
	"fmt"
	bn256 "github.com/mottla/go-AlgebraicProgram-SNARK/pairing"
	"github.com/mottla/go-AlgebraicProgram-SNARK/utils"
	"math/big"
)

var randInput, randOutput = "1@randomIn", "1@randomOut"

type ER1CS struct {
	F        utils.Fields
	indexMap map[string]int
	L        [][]*big.Int
	R        [][]*big.Int
	E        [][]*big.Int
	O        [][]*big.Int
}
type ER1CSSparse struct {
	f        utils.Fields
	indexMap map[string]int
	L        []utils.SparseArray
	R        []utils.SparseArray
	E        []utils.SparseArray
	O        []utils.SparseArray
}
type ER1CSTransposed struct {
	indexMap map[string]int
	L        [][]*big.Int
	R        [][]*big.Int
	E        [][]*big.Int
	O        [][]*big.Int
}

func (er1cs *ER1CS) Transpose() (transposed ER1CSTransposed) {

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
func (er1cs *ER1CSTransposed) ER1CSToEAP(pf utils.Fields) (lPoly, rPoly, ePoly, oPoly [][]*big.Int) {

	lT := er1cs.L
	rT := er1cs.R
	eT := er1cs.E
	oT := er1cs.O
	for i := 0; i < len(lT); i++ {
		lPoly = append(lPoly, pf.PolynomialField.LagrangeInterpolation(lT[i]))

		rPoly = append(rPoly, pf.PolynomialField.LagrangeInterpolation(rT[i]))

		ePoly = append(ePoly, pf.PolynomialField.LagrangeInterpolation(eT[i]))

		oPoly = append(oPoly, pf.PolynomialField.LagrangeInterpolation(oT[i]))
	}

	return
}

//Calculates the witness (program trace) given some extended rank 1 constraint system
//asserts that ER1CS has been computed and is stored in the program p memory calling this function
func CalculateWitness(r1cs *ER1CS, input []InputArgument) (witness []*big.Int, err error) {

	witness = utils.ArrayOfBigZeros(len(r1cs.indexMap))
	set := make([]bool, len(witness))
	witness[0] = big.NewInt(int64(1))
	rnd, rnderr := r1cs.F.CurveOrderField.Rand()
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
		return r1cs.F.ArithmeticField.ScalarProduct(array, witness)
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
			result := r1cs.F.ArithmeticField.Mul(sum(rightKnowns), sum(leftKnowns))
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
			result := r1cs.F.ArithmeticField.Sub(sum(outKnowns), new(bn256.G1).ScalarBaseMult(sum(exponentKnowns)).X())
			result = r1cs.F.ArithmeticField.Div(result, sumright)
			result = r1cs.F.ArithmeticField.Sub(result, sum(leftKnowns))
			result = r1cs.F.ArithmeticField.Div(result, gatesLeftInputs[leftUnknowns[0]]) //divide by a
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
			result := r1cs.F.ArithmeticField.Sub(sum(outKnowns), new(bn256.G1).ScalarBaseMult(sum(exponentKnowns)).X())
			result = r1cs.F.ArithmeticField.Div(result, sumleft)
			result = r1cs.F.ArithmeticField.Sub(result, sum(rightKnowns))
			result = r1cs.F.ArithmeticField.Div(result, gatesRightInputs[rightUnknowns[0]]) //divide by a
			set[rightUnknowns[0]] = true
			witness[rightUnknowns[0]] = result
			continue
		}

		// (a + b + c..) (d+e+..) + (G^(k+v..)) = (F+x*g+..)   we solve for x
		if len(outUnknowns) == 1 {

			result := r1cs.F.ArithmeticField.Mul(sum(rightKnowns), sum(leftKnowns))
			result = r1cs.F.ArithmeticField.Add(result, new(bn256.G1).ScalarBaseMult(sum(exponentKnowns)).X())
			result = r1cs.F.ArithmeticField.Sub(result, sum(outKnowns))
			result = r1cs.F.ArithmeticField.Div(result, gatesOutputs[outUnknowns[0]]) //divide by a
			set[outUnknowns[0]] = true
			witness[outUnknowns[0]] = result
			continue
		}

	}

	return
}

//Calculates the witness (program trace) given some extended rank 1 constraint system
//asserts that ER1CS has been computed and is stored in the program p memory calling this function
//func CalculateWitnessSparse(r1cs *ER1CSSparse, input []*big.Int) (witness utils.SparseArray, err error) {
//
//	witness = utils.NewSparseArray()
//	set := []bool{}
//	witness.InsertNoOverwriteAllowed(uint(0) , big.NewInt(int64(1)))
//	set[0] = true
//
//	//if len(input) > len(witness)-2 {
//	//	panic("inputs missmatch?")
//	//}
//	for i := range input {
//		witness[i+1] = input[i]
//		set[i+1] = true
//	}
//
//	zero := big.NewInt(int64(0))
//
//	getKnownsAndUnknowns := func(array []*big.Int) (knowns []*big.Int, unknownsAtIndices []int) {
//		knowns = utils.ArrayOfBigZeros(len(array))
//		for j, val := range array {
//			if val.Cmp(zero) != 0 {
//				if !set[j] {
//					unknownsAtIndices = append(unknownsAtIndices, j)
//				} else {
//					knowns[j] = val
//				}
//			}
//		}
//		return
//	}
//
//	sum := func(array []*big.Int) *big.Int {
//		return r1cs.F.ArithmeticField.ScalarProduct(array, witness)
//	}
//
//	for i := 0; i < len(r1cs.L); i++ {
//		gatesLeftInputs := r1cs.L[i]
//		gatesRightInputs := r1cs.R[i]
//		gatesExpInputs := r1cs.E[i]
//		gatesOutputs := r1cs.O[i]
//
//		leftKnowns, leftUnknowns := getKnownsAndUnknowns(gatesLeftInputs)
//		rightKnowns, rightUnknowns := getKnownsAndUnknowns(gatesRightInputs)
//		exponentKnowns, exponentUnknowns := getKnownsAndUnknowns(gatesExpInputs)
//		if len(exponentUnknowns) > 0 {
//			return nil, errors.NewSparseArray(fmt.Sprintf("at gate %v: discret logarithm cannot be computed. if you know how. mail me! please!!", i))
//		}
//		outKnowns, outUnknowns := getKnownsAndUnknowns(gatesOutputs)
//
//		//equality gate
//		if len(leftUnknowns)+len(rightUnknowns)+len(outUnknowns) == 0 {
//			result := r1cs.F.ArithmeticField.Mul(sum(rightKnowns), sum(leftKnowns))
//			if result.Cmp(sum(outKnowns)) != 0 {
//				return nil, errors.NewSparseArray(fmt.Sprintf("at equality gate %v there is unequality. %v != %v .We cannot process", i, result.String(), sum(outKnowns).String()))
//			}
//
//		}
//
//		if len(leftUnknowns)+len(rightUnknowns)+len(outUnknowns) > 1 {
//			return nil, errors.NewSparseArray(fmt.Sprintf("at gate %v:computing more then one unknown in Gate assignment is not possible", i))
//		}
//
//		// (a*x + b + c..) (d+e+..) + (G^(k+v..)) = (F+g+..)   we solve for x
//		if len(leftUnknowns) == 1 {
//			sumright := sum(rightKnowns)
//			if sumright.Cmp(zero) == 0 {
//				fmt.Println(r1cs.L[i])
//				fmt.Println(r1cs.R[i])
//				fmt.Println(r1cs.E[i])
//				fmt.Println(r1cs.O[i])
//
//				return nil, errors.NewSparseArray(fmt.Sprintf("at gate %v:the summation of R inputs cannot be 0 if the unknown is in Lexer", i))
//			}
//			result := r1cs.F.ArithmeticField.Sub(sum(outKnowns), new(bn256.G1).ScalarBaseMult(sum(exponentKnowns)).X())
//			result = r1cs.F.ArithmeticField.Div(result, sumright)
//			result = r1cs.F.ArithmeticField.Sub(result, sum(leftKnowns))
//			result = r1cs.F.ArithmeticField.Div(result, gatesLeftInputs[leftUnknowns[0]]) //divide by a
//			set[leftUnknowns[0]] = true
//			witness[leftUnknowns[0]] = result
//			continue
//		}
//		// (a + b + c..) (d+e*x+..) + (G^(k+v..)) = (F+g+..)   we solve for x
//		if len(rightUnknowns) == 1 {
//			sumleft := sum(leftKnowns)
//			if sumleft.Cmp(zero) == 0 {
//				return nil, errors.NewSparseArray(fmt.Sprintf("at gate %v:the summation of Lexer inputs cannot be 0 if the unknown is in R", i))
//			}
//			result := r1cs.F.ArithmeticField.Sub(sum(outKnowns), new(bn256.G1).ScalarBaseMult(sum(exponentKnowns)).X())
//			result = r1cs.F.ArithmeticField.Div(result, sumleft)
//			result = r1cs.F.ArithmeticField.Sub(result, sum(rightKnowns))
//			result = r1cs.F.ArithmeticField.Div(result, gatesRightInputs[rightUnknowns[0]]) //divide by a
//			set[rightUnknowns[0]] = true
//			witness[rightUnknowns[0]] = result
//			continue
//		}
//
//		// (a + b + c..) (d+e+..) + (G^(k+v..)) = (F+x*g+..)   we solve for x
//		if len(outUnknowns) == 1 {
//
//			result := r1cs.F.ArithmeticField.Mul(sum(rightKnowns), sum(leftKnowns))
//			result = r1cs.F.ArithmeticField.Add(result, new(bn256.G1).ScalarBaseMult(sum(exponentKnowns)).X())
//			result = r1cs.F.ArithmeticField.Sub(result, sum(outKnowns))
//			result = r1cs.F.ArithmeticField.Div(result, gatesOutputs[outUnknowns[0]]) //divide by a
//			set[outUnknowns[0]] = true
//			witness[outUnknowns[0]] = result
//			continue
//		}
//
//	}
//
//	return
//}
