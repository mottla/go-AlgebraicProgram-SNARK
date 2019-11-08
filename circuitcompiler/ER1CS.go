package circuitcompiler

import (
	"github.com/mottla/go-AlgebraicProgram-SNARK/circuitcompiler/fields"
	bn256 "github.com/mottla/go-AlgebraicProgram-SNARK/circuitcompiler/pairing"
	"math/big"
)

type ER1CS struct {
	L [][]*big.Int
	R [][]*big.Int
	E [][]*big.Int
	O [][]*big.Int
}
type ER1CSTransposed struct {
	L [][]*big.Int
	R [][]*big.Int
	E [][]*big.Int
	O [][]*big.Int
}

func (er1cs *ER1CS) Transpose() (transposed ER1CSTransposed) {

	transposed.L = fields.Transpose(er1cs.L)
	transposed.R = fields.Transpose(er1cs.R)
	transposed.E = fields.Transpose(er1cs.E)
	transposed.O = fields.Transpose(er1cs.O)
	return
}

//Calculates the witness (program trace) given some input
//asserts that ER1CS has been computed and is stored in the program p memory calling this function
func (r1cs *ER1CS) CalculateWitness(input []*big.Int, f Fields) (witness []*big.Int) {

	witness = fields.ArrayOfBigZeros(len(r1cs.L[0]))
	set := make([]bool, len(witness))
	witness[0] = big.NewInt(int64(1))
	set[0] = true

	for i := range input {
		witness[i+1] = input[i]
		set[i+1] = true
	}

	zero := big.NewInt(int64(0))

	for i := 0; i < len(r1cs.L); i++ {
		gatesLeftInputs := r1cs.L[i]
		gatesRightInputs := r1cs.R[i]
		gatesExpInputs := r1cs.E[i]
		gatesOutputs := r1cs.O[i]

		sumLeft := big.NewInt(int64(0))
		sumRight := big.NewInt(int64(0))
		sumExp := big.NewInt(int64(0))
		sumOut := big.NewInt(int64(0))

		index := -1
		division := false
		for j, val := range gatesLeftInputs {
			if val.Cmp(zero) != 0 {
				if !set[j] {
					index = j
					division = true
					break
				}
				sumLeft.Add(sumLeft, new(big.Int).Mul(val, witness[j]))
			}
		}
		for j, val := range gatesRightInputs {
			if val.Cmp(zero) != 0 {
				sumRight.Add(sumRight, new(big.Int).Mul(val, witness[j]))
			}
		}
		for j, val := range gatesExpInputs {
			if val.Cmp(zero) != 0 {
				sumExp.Add(sumExp, new(big.Int).Mul(val, witness[j]))
			}
		}

		for j, val := range gatesOutputs {
			if val.Cmp(zero) != 0 {
				if !set[j] {
					if index != -1 {
						panic("invalid ER1CS form")
					}

					index = j
					break
				}
				sumOut.Add(sumOut, new(big.Int).Mul(val, witness[j]))
			}
		}

		if !division {
			set[index] = true
			s := f.ArithmeticField.Mul(sumLeft, sumRight)
			exp := new(bn256.G1).ScalarBaseMult(sumExp)
			witness[index] = f.ArithmeticField.Add(s, exp.X())
			s.Add(s, new(big.Int).Exp(new(big.Int).SetInt64(2), sumExp, nil))

		} else {
			set[index] = true
			witness[index] = f.ArithmeticField.Div(sumOut, sumRight)
			//Utils.ArithmeticField.Mul(sumOut, Utils.ArithmeticField.Inverse(sumRight))
		}

	}

	return
}

// R1CSToQAP converts the ER1CS* values to the EAP values
//it uses Lagrange interpolation to to fit a polynomial through each slice. The x coordinate
//is simply a linear increment starting at 1
//within this process, the polynomial is evaluated at position 0
//so an alpha/beta/gamma value is the polynomial evaluated at 0
// the domain polynomial therefor is (-1+x)(-2+x)...(-n+x)
func (er1cs *ER1CSTransposed) ER1CSToEAP(pf Fields) (lPoly, rPoly, ePoly, oPoly [][]*big.Int) {

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
