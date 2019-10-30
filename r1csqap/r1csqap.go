package r1csqap

import (
	"github.com/mottla/go-AlgebraicProgram-SNARK/fields"
	"math/big"
)

type R1CS struct {
	L [][]*big.Int
	R [][]*big.Int
	E [][]*big.Int
	O [][]*big.Int
}

var bigZero = big.NewInt(int64(0))

// Transpose transposes the *big.Int matrix
func Transpose(matrix [][]*big.Int) [][]*big.Int {
	r := make([][]*big.Int, len(matrix[0]))
	for x, _ := range r {
		r[x] = make([]*big.Int, len(matrix))
	}
	for y, s := range matrix {
		for x, e := range s {
			r[x][y] = e
		}
	}
	return r
}

// ArrayOfBigZeros creates a *big.Int array with n elements to zero
func ArrayOfBigZeros(num int) []*big.Int {

	var r = make([]*big.Int, num, num)
	for i := 0; i < num; i++ {
		r[i] = bigZero
	}
	return r
}
func BigArraysEqual(a, b []*big.Int) bool {
	if len(a) != len(b) {
		return false
	}
	for i := 0; i < len(a); i++ {
		if a[i].Cmp(b[i]) != 0 {
			return false
		}
	}
	return true
}

// PolynomialField is the Polynomial over a Finite Field where the polynomial operations are performed
type PolynomialField struct {
	F fields.Fq
}

// NewPolynomialField creates a new PolynomialField with the given FiniteField
func NewPolynomialField(f fields.Fq) PolynomialField {
	return PolynomialField{
		f,
	}
}

// Mul multiplies two polinomials over the Finite Field
func (pf PolynomialField) Mul(a, b []*big.Int) []*big.Int {
	r := ArrayOfBigZeros(len(a) + len(b) - 1)
	for i := 0; i < len(a); i++ {
		for j := 0; j < len(b); j++ {
			r[i+j] = pf.F.Add(
				r[i+j],
				pf.F.Mul(a[i], b[j]))
		}
	}
	return r
}

// Mul multiplies two polinomials over the Finite Field
func (pf PolynomialField) MulSimple(a, b []*big.Int) []*big.Int {
	r := ArrayOfBigZeros(max(len(a), len(b)))
	for i := 0; i < len(a); i++ {
		r[i] = pf.F.Add(r[i], a[i])
	}
	for i := 0; i < len(b); i++ {
		r[i] = pf.F.Mul(r[i], b[i])
	}
	return r
}

// Div divides two polinomials over the Finite Field, returning the result and the remainder
func (pf PolynomialField) Div(a, b []*big.Int) ([]*big.Int, []*big.Int) {
	// https://en.wikipedia.org/wiki/Division_algorithm
	r := ArrayOfBigZeros(len(a) - len(b) + 1)
	rem := a
	for len(rem) >= len(b) {
		l := pf.F.Div(rem[len(rem)-1], b[len(b)-1])
		pos := len(rem) - len(b)
		r[pos] = l
		aux := ArrayOfBigZeros(pos)
		aux1 := append(aux, l)
		aux2 := pf.Sub(rem, pf.Mul(b, aux1))
		rem = aux2[:len(aux2)-1]
	}
	return r, rem
}

func max(a, b int) int {
	if a > b {
		return a
	}
	return b
}

// Add adds two polinomials over the Finite Field
func (pf PolynomialField) Add(a, b []*big.Int) []*big.Int {
	r := ArrayOfBigZeros(max(len(a), len(b)))
	for i := 0; i < len(a); i++ {
		r[i] = pf.F.Add(r[i], a[i])
	}
	for i := 0; i < len(b); i++ {
		r[i] = pf.F.Add(r[i], b[i])
	}
	return r
}

// Sub subtracts two polinomials over the Finite Field
func (pf PolynomialField) Sub(a, b []*big.Int) []*big.Int {
	r := ArrayOfBigZeros(max(len(a), len(b)))
	for i := 0; i < len(a); i++ {
		r[i] = pf.F.Add(r[i], a[i])
	}
	for i := 0; i < len(b); i++ {
		r[i] = pf.F.Sub(r[i], b[i])
	}
	return r
}

// Eval evaluates the polinomial over the Finite Field at the given value x
func (pf PolynomialField) Eval(v []*big.Int, x *big.Int) *big.Int {
	r := big.NewInt(int64(0))
	for i := 0; i < len(v); i++ {
		xi := pf.F.Exp(x, big.NewInt(int64(i)))
		elem := pf.F.Mul(v[i], xi)
		r = pf.F.Add(r, elem)
	}
	return r
}

// NewPolZeroAt generates a new polynomial that has value zero at the given value
func (pf PolynomialField) NewPolZeroAt(pointPos, totalPoints int, height *big.Int) []*big.Int {
	//todo note that this will blow up. big may be necessary
	fac := 1
	//(xj-x0)(xj-x1)..(xj-x_j-1)(xj-x_j+1)..(x_j-x_k)
	for i := 0; i < totalPoints; i++ {
		if i != pointPos {
			fac = fac * (pointPos - i)
		}
	}

	facBig := big.NewInt(int64(fac))
	hf := pf.F.Div(height, facBig)
	r := []*big.Int{hf}
	for i := 0; i < totalPoints; i++ {
		if i != pointPos {
			ineg := big.NewInt(int64(-i))
			b1 := big.NewInt(int64(1))
			r = pf.Mul(r, []*big.Int{ineg, b1})
		}
	}
	return r
}

// LagrangeInterpolation performs the Lagrange Interpolation / Lagrange Polynomials operation
func (pf PolynomialField) LagrangeInterpolation(v []*big.Int) []*big.Int {
	// https://en.wikipedia.org/wiki/Lagrange_polynomial
	var r []*big.Int
	for i := 0; i < len(v); i++ {
		//NOTE this comparison gives a huge performance boost
		//if v[i].Cmp(bigZero) != 0 {
		//	r = pf.Add(r, pf.NewPolZeroAt(i, len(v), v[i]))
		//}
		r = pf.Add(r, pf.NewPolZeroAt(i, len(v), v[i]))

		//r = pf.Mul(v[i], pf.NewPolZeroAt(i+1, len(v), v[i]))
	}
	//
	return r
}

func (er1cs *R1CS) Transpose() (transposed R1CS) {

	transposed.L = Transpose(er1cs.L)
	transposed.R = Transpose(er1cs.R)
	transposed.E = Transpose(er1cs.E)
	transposed.O = Transpose(er1cs.O)
	return
}

// R1CSToQAP converts the R1CS* values to the EAP values
//it uses Lagrange interpolation to to fit a polynomial through each slice. The x coordinate
//is simply a linear increment starting at 1
//within this process, the polynomial is evaluated at position 0
//so an alpha/beta/gamma value is the polynomial evaluated at 0
// the domain polynomial therefor is (-1+x)(-2+x)...(-n+x)
func (pf PolynomialField) ER1CSToEAP(er1cs R1CS) (lPoly, rPoly, ePoly, oPoly [][]*big.Int, domain []*big.Int) {

	lT := er1cs.L
	rT := er1cs.R
	eT := er1cs.E
	oT := er1cs.O
	for i := 0; i < len(lT); i++ {
		lPoly = append(lPoly, pf.LagrangeInterpolation(lT[i]))

		rPoly = append(rPoly, pf.LagrangeInterpolation(rT[i]))

		ePoly = append(ePoly, pf.LagrangeInterpolation(eT[i]))

		oPoly = append(oPoly, pf.LagrangeInterpolation(oT[i]))
	}

	z := []*big.Int{big.NewInt(int64(1))}
	for i := 1; i < len(lT); i++ {
		z = pf.Mul(
			z,
			[]*big.Int{
				pf.F.Neg(
					big.NewInt(int64(i))),
				big.NewInt(int64(1)),
			})
	}
	domain = z
	return
}

//for i := 1; i < len(lT); i++ {
//lT[0] = pf.Add(lT[i], lT[0])
//rT[0] = pf.Add(rT[i], rT[0])
//eT[0] = pf.Add(eT[i], eT[0])
//oT[0] = pf.Add(oT[i], oT[0])
//}
