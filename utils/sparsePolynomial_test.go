package utils

import (
	"fmt"
	bn256 "github.com/mottla/go-AlgebraicProgram-SNARK/pairing"
	"github.com/stretchr/testify/assert"
	"math/big"
	"math/rand"
	"testing"
	"time"
)

func TestEval(t *testing.T) {
	// new Finite Field

	f := NewFq(bn256.Order)
	at, _ := f.Rand()
	//at := big.NewInt(0)
	order := 1000000
	//1 is 100% of the coefficients are 0
	sparsityPercent := 0.9
	a := ArrayOfBigZeros(order)

	for i := 0; i < order; i += 1 + rand.Intn(int(float64(order)*sparsityPercent)) {
		a[i], _ = f.Rand()
	}

	before := time.Now()

	sparseA := NewSparseArray()

	for k, v := range a {
		sparseA.Insert(uint(k), v)
	}

	before = time.Now()
	sparseAt := f.EvalSparsePoly(sparseA, at)
	fmt.Println("evaluate sparse took", time.Since(before))

	before = time.Now()
	classic := f.EvalPoly(a, at)
	fmt.Println("evaluate classic took", time.Since(before))

	//fmt.Println(f.EvalSparsePoly(sparseC,b16).String())
	if sparseAt.Cmp(classic) != 0 {
		t.Error(fmt.Sprintf("classic poly %v and sparse poly %v evaluation differ. At leas one of both must be wrong", sparseAt.String(), classic.String()))
	}

}

func TestMultiply(t *testing.T) {
	// new Finite Field

	f := NewFq(bn256.Order)
	at, _ := f.Rand()

	order := 1000
	//1 is 100% of the coefficients are 0
	sparsityPercent := 0.1
	a := ArrayOfBigZeros(order)
	b := ArrayOfBigZeros(order)
	for i := 0; i < order; i += 1 + rand.Intn(int(float64(order)*sparsityPercent)) {
		a[i], _ = f.Rand()
	}
	for i := 0; i < order; i += 1 + rand.Intn(int(float64(order)*sparsityPercent)) {
		b[i], _ = f.Rand()
	}
	// new Polynomial Field
	pf := NewPolynomialFieldPrecomputedLagriangian(f, 100)

	before := time.Now()
	c := pf.Mul(a, b)
	fmt.Println("multiply with horner took", time.Since(before))

	sparseA := NewSparseArray()
	sparseB := NewSparseArray()
	for k, v := range a {
		sparseA.Insert(uint(k), v)
	}
	for k, v := range b {
		sparseB.Insert(uint(k), v)
	}
	before = time.Now()
	sparseC := f.MulSparse(sparseA, sparseB)
	fmt.Println("multiply sparse took", time.Since(before))
	before = time.Now()
	sparseAt := f.EvalSparsePoly(sparseC, at)
	fmt.Println("evaluate sparse took", time.Since(before))

	before = time.Now()
	classic := f.EvalPoly(c, at)
	fmt.Println("evaluate classic took", time.Since(before))

	//fmt.Println(f.EvalSparsePoly(sparseC,b16).String())
	if sparseAt.Cmp(classic) != 0 {
		t.Error(fmt.Sprintf("classic poly %v and sparse poly %v evaluation differ. At leas one of both must be wrong", sparseAt.String(), classic.String()))
	}

}

func TestAdd(t *testing.T) {
	// new Finite Field

	f := NewFq(bn256.Order)
	at, _ := f.Rand()

	order := 10000
	//1 is 100% of the coefficients are 0
	sparsityPercent := 0.1
	a := ArrayOfBigZeros(order)
	b := ArrayOfBigZeros(order)
	for i := 0; i < order; i += 1 + rand.Intn(int(float64(order)*sparsityPercent)) {
		a[i], _ = f.Rand()
	}
	for i := 0; i < order; i += 1 + rand.Intn(int(float64(order)*sparsityPercent)) {
		b[i], _ = f.Rand()
	}
	// new Polynomial Field
	pf := NewPolynomialFieldPrecomputedLagriangian(f, 100)

	before := time.Now()
	c := pf.Add(a, b)
	fmt.Println("add classic took", time.Since(before))

	sparseA := NewSparseArray()
	sparseB := NewSparseArray()
	for k, v := range a {
		sparseA.Insert(uint(k), v)
	}
	for k, v := range b {
		sparseB.Insert(uint(k), v)
	}
	before = time.Now()
	sparseC := f.AddSparse(sparseA, sparseB)
	fmt.Println("add sparse took", time.Since(before))
	before = time.Now()
	sparseAt := f.EvalSparsePoly(sparseC, at)
	fmt.Println("evaluate sparse took", time.Since(before))

	before = time.Now()
	classic := f.EvalPoly(c, at)
	fmt.Println("evaluate classic took", time.Since(before))

	//fmt.Println(f.EvalSparsePoly(sparseC,b16).String())
	if sparseAt.Cmp(classic) != 0 {
		t.Error(fmt.Sprintf("classic poly %v and sparse poly %v evaluation differ. At leas one of both must be wrong", sparseAt.String(), classic.String()))
	}

}

func TestSub(t *testing.T) {
	// new Finite Field

	f := NewFq(bn256.Order)
	at, _ := f.Rand()

	order := 10000
	//1 is 100% of the coefficients are 0
	sparsityPercent := 0.1
	a := ArrayOfBigZeros(order)
	b := ArrayOfBigZeros(order)
	for i := 0; i < order; i += 1 + rand.Intn(int(float64(order)*sparsityPercent)) {
		a[i], _ = f.Rand()
	}
	for i := 0; i < order; i += 1 + rand.Intn(int(float64(order)*sparsityPercent)) {
		b[i], _ = f.Rand()
	}
	// new Polynomial Field
	pf := NewPolynomialFieldPrecomputedLagriangian(f, 100)

	before := time.Now()
	c := pf.Sub(a, b)
	fmt.Println("sub classic took", time.Since(before))

	sparseA := NewSparseArray()
	sparseB := NewSparseArray()
	for k, v := range a {
		sparseA.Insert(uint(k), v)
	}
	for k, v := range b {
		sparseB.Insert(uint(k), v)
	}
	before = time.Now()
	sparseC := f.SubSparse(sparseA, sparseB)
	fmt.Println("sub sparse took", time.Since(before))
	before = time.Now()
	sparseAt := f.EvalSparsePoly(sparseC, at)
	fmt.Println("evaluate sparse took", time.Since(before))

	before = time.Now()
	classic := f.EvalPoly(c, at)
	fmt.Println("evaluate classic took", time.Since(before))

	//fmt.Println(f.EvalSparsePoly(sparseC,b16).String())
	if sparseAt.Cmp(classic) != 0 {
		t.Error(fmt.Sprintf("classic poly %v and sparse poly %v evaluation differ. At leas one of both must be wrong", sparseAt.String(), classic.String()))
	}

}
func TestSub2(t *testing.T) {
	// new Finite Field

	f := NewFq(bn256.Order)
	at, _ := f.Rand()

	order := 2000
	sparsityPercent := 0.4
	a := ArrayOfBigZeros(order * 2)
	b := ArrayOfBigZeros(order)
	for i := 0; i < order*2; i += 1 + rand.Intn(int(float64(order)*sparsityPercent)) {
		a[i], _ = f.Rand()
		//a[i]=big.NewInt(int64(i))
	}
	for i := 0; i < order; i += 1 + rand.Intn(int(float64(order)*sparsityPercent)) {
		b[i], _ = f.Rand()
		//b[i]=big.NewInt(int64(i))
	}
	//a[0]=big.NewInt(-1)
	//a[1]=big.NewInt(0)
	//a[2]=big.NewInt(2)
	//b[0]=big.NewInt(0)
	//b[1]=big.NewInt(1)
	before := time.Now()
	sparseA := NewSparseArray()
	sparseB := NewSparseArray()
	for k, v := range a {
		sparseA.Insert(uint(k), v)
	}
	for k, v := range b {
		sparseB.Insert(uint(k), v)
	}

	before = time.Now()
	cDivSparse := f.SubSparse(sparseA, sparseB)
	fmt.Println("sub sparse took", time.Since(before))

	//sparseA - sparseB= cDivSparse
	cd := f.AddSparse(cDivSparse, sparseB)

	classic1 := f.EvalSparsePoly(cd, at)
	classic2 := f.EvalSparsePoly(sparseA, at)

	//fmt.Println(f.EvalSparsePoly(sparseC,b16).String())
	if classic1.Cmp(classic2) != 0 {
		t.Error(fmt.Sprintf("classic poly %v and sparse poly %v evaluation differ. At leas one of both must be wrong", classic1.String(), classic2.String()))
	}

}

func TestDivide2(t *testing.T) {
	// new Finite Field

	f := NewFq(bn256.Order)
	at, _ := f.Rand()

	order := 2000
	sparsityPercent := 0.1
	a := ArrayOfBigZeros(order * 2)
	b := ArrayOfBigZeros(order)
	for i := 0; i < order*2; i += 1 + rand.Intn(int(float64(order)*sparsityPercent)) {
		a[i], _ = f.Rand()
		//a[i]=big.NewInt(int64(i))
	}
	for i := 0; i < order; i += 1 + rand.Intn(int(float64(order)*sparsityPercent)) {
		b[i], _ = f.Rand()
		//b[i]=big.NewInt(int64(i))
	}
	before := time.Now()
	sparseA := NewSparseArray()
	sparseB := NewSparseArray()
	for k, v := range a {
		sparseA.Insert(uint(k), v)
	}
	for k, v := range b {
		sparseB.Insert(uint(k), v)
	}

	before = time.Now()
	cDivSparse, rem2 := f.DivideSparse(sparseA, sparseB)
	fmt.Println("c:" + cDivSparse.String())
	fmt.Println("rem" + rem2.String())
	fmt.Println("sparse division took", time.Since(before))

	//sparseA=CdivSparece*sparseB +rem2
	mul := f.MulSparse(cDivSparse, sparseB)
	cd := f.AddSparse(mul, rem2)

	classic1 := f.EvalSparsePoly(cd, at)
	classic2 := f.EvalSparsePoly(sparseA, at)

	//fmt.Println(f.EvalSparsePoly(sparseC,b16).String())
	if classic1.Cmp(classic2) != 0 {
		t.Error(fmt.Sprintf("classic poly %v and sparse poly %v evaluation differ. At leas one of both must be wrong", classic1.String(), classic2.String()))
	}

}

func TestDivide(t *testing.T) {
	// new Finite Field

	f := NewFq(bn256.Order)
	at, _ := f.Rand()

	order := 2000
	sparsityPercent := 0.1
	a := ArrayOfBigZeros(order * 2)
	b := ArrayOfBigZeros(order)
	for i := 0; i < order*2; i += 1 + rand.Intn(1+int(float64(order)*sparsityPercent)) {
		a[i], _ = f.Rand()
		//a[i]=big.NewInt(int64(i))
	}
	for i := 0; i < order; i += 1 + rand.Intn(1+int(float64(order)*sparsityPercent)) {
		b[i], _ = f.Rand()
		//b[i]=big.NewInt(int64(i))
	}

	before := time.Now()
	sparseA := NewSparseArray()
	sparseB := NewSparseArray()
	for k, v := range a {
		sparseA.Insert(uint(k), v)
	}
	for k, v := range b {
		sparseB.Insert(uint(k), v)
	}

	before = time.Now()
	cDivSparse, rem2 := f.DivideSparse(sparseA, sparseB)
	fmt.Println("sparse division took", time.Since(before))

	//sparseA:sparseB=CdivSparece +rem2
	cd := f.AddSparse(f.MulSparse(cDivSparse, sparseB), rem2)
	classic1 := f.EvalSparsePoly(cd, at)
	classic2 := f.EvalSparsePoly(sparseA, at)

	//fmt.Println(f.EvalSparsePoly(sparseC,b16).String())
	if classic1.Cmp(classic2) != 0 {
		t.Error(fmt.Sprintf("classic poly %v and sparse poly %v evaluation differ. At leas one of both must be wrong", classic1.String(), classic2.String()))
	}

}

func TestSparseLagrangeInterpolation(t *testing.T) {
	// new Finite Field
	var Npoints = int64(100)
	r := new(big.Int).Set(bn256.P)
	f := NewFq(r)
	// new Polynomial Field
	pf := NewPolynomialFieldPrecomputedLagriangian(f, int(Npoints))

	var err error

	Xpoints := make([]*big.Int, Npoints)
	for i := int64(0); i < Npoints; i++ {
		Xpoints[i] = new(big.Int).SetInt64(i)
	}

	Ypoints := make([]*big.Int, Npoints)

	for i := int64(0); i < Npoints; i++ {
		Ypoints[i], err = f.Rand()
		assert.Nil(t, err)
	}
	Ypoints[3] = new(big.Int).SetInt64(int64(0))
	sparse := NewSparseArrayFromArray(Ypoints)
	sparse = pf.F.InterpolateSparseArray(sparse)
	alpha := pf.LagrangeInterpolation(Ypoints)
	for i := int64(0); i < Npoints; i++ {
		if f.EvalPoly(alpha, Xpoints[i]).Cmp(Ypoints[i]) != 0 {
			t.Error("fail")
		}
		if f.EvalSparsePoly(sparse, Xpoints[i]).Cmp(Ypoints[i]) != 0 {
			t.Error(fmt.Sprintf("fail sparse %v", i))
		} else {
			fmt.Printf("sicces at %v \n", i)
		}

	}

}
