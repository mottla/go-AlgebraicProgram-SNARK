package utils

import (
	"fmt"
	"math/big"
)

// Mul multiplies two polinomials over the Finite Field
func (fq Fq) MulSparse(a, b SparseArray) SparseArray {
	r := NewSparseArray()

	for L := range a.ChannelNodes(true) {
		for R := range b.ChannelNodes(true) {
			r.push(L.Key+R.Key, fq.Mul(R.Value, L.Value), fq.Add)
		}
	}
	return r
}

// Div divides two polinomials over the Finite Field, returning the result and the remainder
func (fq Fq) DivideSparse(a, b SparseArray) (result SparseArray, rem SparseArray) {
	result = NewSparseArray()
	rem = a
	maxA, maxB := rem.MaxNode(), b.MaxNode()
	for ; maxA != nil && maxB != nil && maxA.Key >= maxB.Key; maxA = rem.MaxNode() {
		l := fq.Div(maxA.Value, maxB.Value)
		pos := maxA.Key - maxB.Key
		aux := NewSparseArray()
		aux.InsertNoOverwriteAllowed(pos, l)
		result.InsertNoOverwriteAllowed(pos, l)
		mul := fq.MulSparse(b, aux)
		rem = fq.SubSparse(rem, mul)
	}
	return result, rem
}

// Add adds two polinomials over the Finite Field
func (fq Fq) AddSparse(a, b SparseArray) SparseArray {
	r := NewSparseArray()

	for v := range a.ChannelNodes(false) {
		r.push(v.Key, v.Value, fq.Add)
	}
	for v := range b.ChannelNodes(false) {
		r.push(v.Key, v.Value, fq.Add)
	}
	return r
}

//EvalPoly Evaluates a sparse polynomial
func (fq Fq) EvalSparsePoly(poly SparseArray, at *big.Int) (result *big.Int) {
	//get the number of bits of the highest degree
	nBits := len(fmt.Sprintf("%b", poly.Degree()))
	if nBits < poly.Count() {
		fmt.Println("WARN, ur polynomial is not very sparse. a casual array type polynomial becomes more efficient at some point. not necessarily in this case however.")
	}
	if at.Cmp(bigZero) == 0 {
		if v, b := poly.Exists(0); v {
			return new(big.Int).Set(b)
		}
		return big.NewInt(0)
	}
	//tree that stores intermediate results of exponent ladder. Key is the exponent. value is at^key
	alredyComputedExponents := NewSparseArray()
	alredyComputedExponents.InsertNoOverwriteAllowed(1, at)
	result = new(big.Int).SetInt64(0)
	for j := range poly.ChannelNodes(true) {
		rem := j.Key
		q := uint(0)
		nextPower := new(big.Int).SetInt64(1)
		arr := alredyComputedExponents.DecendingNodes()
		for _, highestAlreadyComputedExponent := range arr {
			q, rem = euclid(rem, highestAlreadyComputedExponent.Key)
			vv := fq.ExpInt(highestAlreadyComputedExponent.Value, q)
			alredyComputedExponents.Insert(q*highestAlreadyComputedExponent.Key, vv)
			nextPower = fq.Mul(nextPower, vv)
			if rem == 0 {
				break
			}
		}
		result = fq.Add(result, fq.Mul(j.Value, nextPower))
	}
	return result
}

//euclid returns q,r s.t. a=bq+r
func euclid(a, b uint) (q, r uint) {
	if b == 0 {
		panic("not allowed")
	}

	return a / b, a % b
}

// Sub subtracts two polinomials over the Finite Field
func (fq Fq) SubSparse(a, b SparseArray) SparseArray {
	r := NewSparseArray()
	for v := range a.ChannelNodes(false) {
		r.push(v.Key, v.Value, fq.Add)
	}
	for v := range b.ChannelNodes(false) {
		r.push(v.Key, fq.Neg(v.Value), fq.Add)
	}
	return r
}

// LagrangeInterpolation performs the Lagrange Interpolation / Lagrange Polynomials operation
func (f Fq) InterpolateSparseArray(dataArray SparseArray) (polynom SparseArray) {
	// https://en.wikipedia.org/wiki/Lagrange_polynomial

	var base = func(pointPos, totalPoints uint) (r SparseArray) {
		var iterator = new(big.Int)
		facBig := big.NewInt(1)

		for i := uint(0); i < pointPos; i++ {
			iterator.SetInt64(int64(pointPos - i))
			facBig = f.Mul(facBig, iterator)
		}
		for i := pointPos + 1; i < totalPoints; i++ {
			iterator.SetInt64(int64(pointPos - i))
			facBig = f.Mul(facBig, iterator)
		}
		hf := f.Inverse(facBig)
		r = NewSparseArrayWith(uint(0), hf)
		for i := uint(0); i < totalPoints; i++ {
			if i != pointPos {
				r = f.MulSparse(r, NewSparseArrayFromArray([]*big.Int{big.NewInt(int64(-i)), big.NewInt(int64(1))}))
			}
		}
		return r
	}

	maxDegree := dataArray.MaxNode().Key
	for v := range dataArray.ChannelNodes(true) {

		polynom = f.AddSparse(polynom, f.MulSparse(base(v.Key, maxDegree+1), NewSparseArrayWith(uint(0), v.Value)))

	}
	return polynom
}

//
func (f Fq) LinearCombine(polynomials []SparseArray, w []*big.Int) (scaledPolynomials []SparseArray) {
	scaledPolynomials = make([]SparseArray, len(w))
	for i := 0; i < len(w); i++ {
		scaledPolynomials[i] = f.MulSparse(NewSparseArrayWith(uint(0), w[i]), polynomials[i])

	}
	return
}
func (f Fq) AddPolynomials(polynomials []SparseArray) (sumPoly SparseArray) {
	for i := 0; i < len(polynomials); i++ {
		sumPoly = f.AddSparse(sumPoly, polynomials[i])
	}
	return
}
