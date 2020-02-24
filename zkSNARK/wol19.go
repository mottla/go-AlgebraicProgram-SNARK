package zkSNARK

import (
	"bytes"
	"fmt"
	"github.com/mottla/go-AlgebraicProgram-SNARK/circuitcompiler"
	bn256 "github.com/mottla/go-AlgebraicProgram-SNARK/pairing"
	"github.com/mottla/go-AlgebraicProgram-SNARK/utils"
	"math/big"
)

type Pk struct {
	// Proving Key

	Domain            []*big.Int
	eGH, eGHalphaBeta *bn256.GT

	G1 struct {
		RLEO_Delta           []*bn256.G1 // {( αRi(x)+βLi(x)+βEi(x)+Oi(x) ) / δ } from l+1 to m
		Alpha                *bn256.G1
		Beta                 *bn256.G1
		Delta                *bn256.G1
		RLEO_Gamma           []*bn256.G1 // {( αRi(x)+βLi(x)+βEi(x)+Oi(x) ) / γ } from 0 to l
		PowersX              []*bn256.G1
		PowersX_Domain_Delta []*bn256.G1 // { G1^( (x^i D(x)) / delta} from 0 to n-1
		Lx_plus_Ex           []*bn256.G1 // G^ Ei(x)+Li(x)   from 0 to m
		Ex                   []*bn256.G1 // G^ Ei(x)  from 0 to m
	}
	G2 struct {
		Beta    *bn256.G2
		Gamma   *bn256.G2
		Delta   *bn256.G2
		PowersX []*bn256.G2
		Rx      []*bn256.G2 // G^ Ri(x)   from 0 to m
	}
}

//type Vk struct {
//	IC [][3]*big.Int
//	G1 struct {
//		Alpha [3]*big.Int
//	}
//	G2 struct {
//		Beta  [3][2]*big.Int
//		Gamma [3][2]*big.Int
//		Delta [3][2]*big.Int
//	}
//}

// Setup is the data structure holding the Trusted Setup data. The Setup.Toxic sub struct must be destroyed after the GenerateTrustedSetup function is completed
type Setup struct {
	Toxic struct {
		x      *big.Int // trusted setup secret
		Kalpha *big.Int
		Kbeta  *big.Int
		Kgamma *big.Int
		Kdelta *big.Int
	}

	// public
	Pk Pk
	//Vk Vk
}

// Proof contains the parameters to proof the zkSNARK
type Proof struct {
	PiA *bn256.G1
	PiB *bn256.G2
	PiC *bn256.G1
	PiF *bn256.G1
}

// CombinePolynomials combine the given polynomials arrays into one, also returns the P(x)
func CombinePolynomials2(fields utils.Fields, witness []*big.Int, TransposedR1cs circuitcompiler.ER1CSTransposed) (Gx, Px []*big.Int) {

	pf := fields.PolynomialField

	scalarProduct := func(vec [][]*big.Int) (poly []*big.Int) {
		var ax []*big.Int
		for i := 0; i < len(witness); i++ {
			m := pf.Mul([]*big.Int{witness[i]}, vec[i])
			ax = pf.Add(ax, m)
		}
		return ax
	}
	//note thate we could first multiply, add and sub with the datapoints and then interpolate.
	//however after the multiplication, the degree is higher. interpolation time is
	//quadratic to the degree. Therefor its more efficient to interpolate and then operate.
	//however.. the datapoints are sparse. if i interpolate them. they wont be sparse any longer
	//multiplication takes full square time.
	//most efficient is therfor precomputing lagrange bases, interpolate and then perform the operations.
	LVec := pf.LagrangeInterpolation(scalarProduct(TransposedR1cs.L))
	RVec := pf.LagrangeInterpolation(scalarProduct(TransposedR1cs.R))
	EVec := scalarProduct(TransposedR1cs.E)
	OVec := pf.LagrangeInterpolation(scalarProduct(TransposedR1cs.O))

	var mG_pointsVec []*big.Int
	for i := 0; i < len(EVec); i++ {
		p := g1ScalarBaseMultiply(EVec[i])
		mG_pointsVec = append(mG_pointsVec, p.X())
	}
	Gx = pf.LagrangeInterpolation(mG_pointsVec)
	a := pf.Mul(LVec, RVec)
	b := pf.Add(a, Gx)
	c := pf.Sub(b, OVec)
	return Gx, c
}

//func CombinePolynomials3(fields utils.Fields, witness []*big.Int, TransposedR1cs circuitcompiler.ER1CSTransposed) (Gx, Px []*big.Int) {
//
//	pf := fields.PolynomialField
//
//	scalarProduct := func(vec [][]*big.Int) (poly []*big.Int) {
//		var ax []*big.Int
//		for i := 0; i < len(witness); i++ {
//			m := pf.Mul([]*big.Int{witness[i]}, vec[i])
//			ax = pf.Add(ax, m)
//		}
//		return ax
//	}
//
//	LVec := (scalarProduct(TransposedR1cs.L))
//	RVec := (scalarProduct(TransposedR1cs.R))
//	EVec := scalarProduct(TransposedR1cs.E)
//	OVec := (scalarProduct(TransposedR1cs.O))
//
//	var mG_pointsVec []*big.Int
//	for i := 0; i < len(EVec); i++ {
//		p := g1ScalarBaseMultiply(EVec[i])
//		mG_pointsVec = append(mG_pointsVec, p.X())
//	}
//	Gx = pf.LagrangeInterpolation(mG_pointsVec)
//	a := pf.Mul(LVec, RVec)
//	b := pf.Add(a, Gx)
//	c := pf.Sub(b, OVec)
//	return Gx, pf.LagrangeInterpolation(c)
//}

// CombinePolynomials combine the given polynomials arrays into one, also returns the P(x)
func CombinePolynomials(fields utils.Fields, witness []*big.Int, Li, Ri, Ei, Oi [][]*big.Int) (Gx, Px []*big.Int) {

	pf := fields.PolynomialField

	LVec := pf.AddPolynomials(pf.LinearCombine(Li, witness))
	RVec := pf.AddPolynomials(pf.LinearCombine(Ri, witness))
	EVec := pf.AddPolynomials(pf.LinearCombine(Ei, witness))
	OVec := pf.AddPolynomials(pf.LinearCombine(Oi, witness))

	var mG_pointsVec []*big.Int
	for i := 0; i < len(EVec); i++ {
		val := fields.ArithmeticField.EvalPoly(EVec, new(big.Int).SetInt64(int64(i)))
		p := g1ScalarBaseMultiply(val)
		mG_pointsVec = append(mG_pointsVec, p.X())
	}
	Gx = pf.LagrangeInterpolation(mG_pointsVec)
	a := pf.Mul(LVec, RVec)
	b := pf.Add(a, Gx)
	c := pf.Sub(b, OVec)
	return Gx, c
}

//CombinePolynomials combine the given polynomials arrays into one, also returns the P(x)
func CombineSparsePolynomials(f utils.Fields, witness []*big.Int, TransposedR1cs circuitcompiler.ER1CSsPARSETransposed) (Gx, Px *utils.AvlTree) {

	pf := f.ArithmeticField

	scalarProduct := func(vec []*utils.AvlTree) (poly *utils.AvlTree) {
		poly = pf.AddPolynomials(pf.LinearCombine(vec, witness))
		return
	}

	LVec := scalarProduct(TransposedR1cs.L)
	RVec := scalarProduct(TransposedR1cs.R)
	EVec := scalarProduct(TransposedR1cs.E)
	OVec := scalarProduct(TransposedR1cs.O)

	var mG_pointsVec = utils.NewAvlTree()
	for v := range EVec.ChannelNodes(true) {
		p := g1ScalarBaseMultiply(v.Value)
		mG_pointsVec.InsertNoOverwriteAllowed(v.Key, p.X())
	}
	Gx = pf.InterpolateSparseArray(mG_pointsVec, TransposedR1cs.MaxKey)
	a := pf.MulSparse(LVec, RVec)
	pf.AddToSparse(a, mG_pointsVec)
	pf.SubToSparse(a, OVec)

	return Gx, pf.InterpolateSparseArray(a, TransposedR1cs.MaxKey)
}

func g1ScalarBaseMultiply(in *big.Int) *bn256.G1 {
	return new(bn256.G1).ScalarBaseMult(in)
}
func g2ScalarBaseMultiply(in *big.Int) *bn256.G2 {
	return new(bn256.G2).ScalarBaseMult(in)
}

// GenerateTrustedSetup generates the Trusted Setup from a compiled Circuit. The Setup.Toxic sub data structure must be destroyed
func GenerateTrustedSetup(fields utils.Fields, witnessLength, gates, publicinputs int, Li, Ri, Ei, Oi [][]*big.Int) (*Setup, error) {
	var setup = new(Setup)
	var err error

	// generate random t value
	setup.Toxic.x, err = fields.CurveOrderField.Rand()
	if err != nil {
		panic("random failed")
	}
	//TODO this is why my scheme sucks. we can only have x in {0,..,len(gates)} and not from the entire field. This destroys security
	setup.Toxic.x = new(big.Int).SetInt64(1)

	setup.Toxic.Kalpha, err = fields.CurveOrderField.Rand()
	if err != nil {
		panic("random failed")
	}
	setup.Toxic.Kbeta, err = fields.CurveOrderField.Rand()
	if err != nil {
		panic("random failed")
	}
	setup.Toxic.Kgamma, err = fields.CurveOrderField.Rand()
	if err != nil {
		panic("random failed")
	}
	setup.Toxic.Kdelta, err = fields.CurveOrderField.Rand()
	if err != nil {
		panic("random failed")
	}

	//generate the domain polynomial
	Domain := []*big.Int{big.NewInt(int64(1))}

	//(x)(x-1)(x-2)..TODO maybe here index
	for i := 0; i < gates; i++ {
		Domain = fields.PolynomialField.Mul(
			Domain,
			[]*big.Int{
				fields.ArithmeticField.Neg(big.NewInt(int64(i))), big.NewInt(int64(1)),
			})
	}

	setup.Pk.Domain = Domain
	//TODO other field maybe??
	Dx := fields.CurveOrderField.EvalPoly(Domain, setup.Toxic.x)
	invDelta := fields.CurveOrderField.Inverse(setup.Toxic.Kdelta)
	invgamma := fields.CurveOrderField.Inverse(setup.Toxic.Kgamma)
	Dx_div_delta := fields.CurveOrderField.Mul(invDelta, Dx)

	// encrypt x values with curve generators
	// x^i times D(x) divided by delta
	var powersXDomaindivDelta = []*bn256.G1{g1ScalarBaseMultiply(Dx_div_delta)}
	var powersX_onG = []*bn256.G1{g1ScalarBaseMultiply(big.NewInt(1))}
	var powersX_onH = []*bn256.G2{g2ScalarBaseMultiply(big.NewInt(1))}

	//G^{x^i}
	tEncr := new(big.Int).Set(setup.Toxic.x)
	for i := 1; i < len(Ri); i++ {
		powersXDomaindivDelta = append(powersXDomaindivDelta, g1ScalarBaseMultiply(fields.CurveOrderField.Mul(tEncr, Dx_div_delta)))
		powersX_onG = append(powersX_onG, g1ScalarBaseMultiply(tEncr))
		powersX_onH = append(powersX_onH, g2ScalarBaseMultiply(tEncr))
		// x^i -> x^{i+1}
		tEncr = fields.CurveOrderField.Mul(tEncr, setup.Toxic.x)
	}

	setup.Pk.G1.PowersX = powersX_onG
	setup.Pk.G2.PowersX = powersX_onH
	setup.Pk.G1.PowersX_Domain_Delta = powersXDomaindivDelta

	setup.Pk.G1.Alpha = g1ScalarBaseMultiply(setup.Toxic.Kalpha)
	setup.Pk.G1.Beta = g1ScalarBaseMultiply(setup.Toxic.Kbeta)
	setup.Pk.G1.Delta = g1ScalarBaseMultiply(setup.Toxic.Kdelta)

	setup.Pk.G2.Beta = g2ScalarBaseMultiply(setup.Toxic.Kbeta)
	setup.Pk.G2.Gamma = g2ScalarBaseMultiply(setup.Toxic.Kgamma)
	setup.Pk.G2.Delta = g2ScalarBaseMultiply(setup.Toxic.Kdelta)

	for i := 0; i < witnessLength; i++ {
		// Li(x) Todo here??
		lix := fields.CurveOrderField.EvalPoly(Li[i], setup.Toxic.x)
		// Ri(x)
		rix := fields.CurveOrderField.EvalPoly(Ri[i], setup.Toxic.x)
		// Oi(x)
		oix := fields.CurveOrderField.EvalPoly(Oi[i], setup.Toxic.x)

		// Ei(x)
		eix := fields.CurveOrderField.EvalPoly(Ei[i], setup.Toxic.x)
		setup.Pk.G1.Ex = append(setup.Pk.G1.Ex, g1ScalarBaseMultiply(eix))

		setup.Pk.G1.Lx_plus_Ex = append(setup.Pk.G1.Lx_plus_Ex, g1ScalarBaseMultiply(fields.CurveOrderField.Add(eix, lix)))

		//H^Rix
		hRix := g2ScalarBaseMultiply(fields.CurveOrderField.Copy(rix))
		setup.Pk.G2.Rx = append(setup.Pk.G2.Rx, hRix)

		ter := fields.CurveOrderField.Mul(setup.Toxic.Kalpha, rix)
		ter = fields.CurveOrderField.Add(ter, fields.CurveOrderField.Mul(setup.Toxic.Kbeta, lix))
		ter = fields.CurveOrderField.Add(ter, fields.CurveOrderField.Mul(setup.Toxic.Kbeta, eix))
		ter = fields.CurveOrderField.Add(ter, oix)

		if i <= publicinputs {
			ter = fields.CurveOrderField.Mul(invgamma, ter)
			setup.Pk.G1.RLEO_Gamma = append(setup.Pk.G1.RLEO_Gamma, g1ScalarBaseMultiply(ter))
		} else {
			ter = fields.CurveOrderField.Mul(invDelta, ter)
			setup.Pk.G1.RLEO_Delta = append(setup.Pk.G1.RLEO_Delta, g1ScalarBaseMultiply(ter))
		}
	}
	setup.Pk.eGH = bn256.Pair(g1ScalarBaseMultiply(new(big.Int).SetInt64(1)), g2ScalarBaseMultiply(new(big.Int).SetInt64(1)))
	//is a field multiplication under order g1 wrong?
	setup.Pk.eGHalphaBeta = bn256.Pair(g1ScalarBaseMultiply(setup.Toxic.Kalpha), g2ScalarBaseMultiply(setup.Toxic.Kbeta))
	//fmt.Println("zsfdadsff")
	//fmt.Println(setup.Pk.eGHalphaBeta.String() )
	//setup.Pk.eGHalphaBeta = new(bn256.GT).ScalarMult(setup.Pk.eGH, fields.ArithmeticField.Mul(setup.Toxic.Kalpha, setup.Toxic.Kbeta))
	//fmt.Println(setup.Pk.eGHalphaBeta.String() )
	return setup, nil
}

// GenerateProofs generates all the parameters to proof the zkSNARK from the Circuit, Setup and the Witness
func GenerateProofs(f utils.Fields, witnessLength, publicInputs int, pk *Pk, w []*big.Int, Px []*big.Int) (*Proof, error) {
	var proof = new(Proof)
	proof.PiA = new(bn256.G1).ScalarMult(pk.G1.Lx_plus_Ex[0], w[0])
	proof.PiB = new(bn256.G2).ScalarMult(pk.G2.Rx[0], w[0])
	proof.PiC = new(bn256.G1).ScalarMult(pk.G1.RLEO_Delta[0], w[publicInputs+1])
	proof.PiF = new(bn256.G1).ScalarMult(pk.G1.Ex[0], w[0])
	Qx, r := f.PolynomialField.Div(Px, pk.Domain)

	if !utils.IsZeroArray(r) {
		panic("remainder supposed to be 0")
	}

	var QxDx_div_delta = new(bn256.G1).ScalarMult(pk.G1.PowersX_Domain_Delta[0], Qx[0])

	for i := 1; i < len(Qx); i++ {
		tmp := new(bn256.G1).ScalarMult(pk.G1.PowersX_Domain_Delta[i], Qx[i])
		QxDx_div_delta.Add(QxDx_div_delta, tmp)
	}

	for i := 1; i < witnessLength; i++ {
		//proof element A
		proof.PiA.Add(proof.PiA, new(bn256.G1).ScalarMult(pk.G1.Lx_plus_Ex[i], w[i]))

		//proof element B
		proof.PiB.Add(proof.PiB, new(bn256.G2).ScalarMult(pk.G2.Rx[i], w[i]))

		if i > publicInputs+1 {
			//proof element C
			proof.PiC.Add(proof.PiC, new(bn256.G1).ScalarMult(pk.G1.RLEO_Delta[i-publicInputs-1], w[i]))
		}
		//proof element F
		proof.PiF.Add(proof.PiF, new(bn256.G1).ScalarMult(pk.G1.Ex[i], w[i]))
	}
	//add the alpha therm to proof element A
	proof.PiA.Add(proof.PiA, pk.G1.Alpha)

	//add the Q(x)D(x)/delta therm to the proof element C
	proof.PiC.Add(proof.PiC, QxDx_div_delta)

	return proof, nil
}

// VerifyProof verifies over the BN256 the Pairings of the Proof
func VerifyProof(pk *Pk, proof *Proof, publicSignals []*big.Int, debug bool) bool {
	//note that the trivial cases should be rejected to

	if len(publicSignals) != len(pk.G1.RLEO_Gamma) {
		fmt.Println("❌ wolf19 verification not passed. Signal length wrong")
		return false
	}

	icPubl := new(bn256.G1).ScalarMult(pk.G1.RLEO_Gamma[0], publicSignals[0])
	for i := 1; i < len(publicSignals); i++ {
		icPubl.Add(icPubl, new(bn256.G1).ScalarMult(pk.G1.RLEO_Gamma[i], publicSignals[i]))
	}

	a := bn256.Pair(proof.PiA, new(bn256.G2).Add(proof.PiB, pk.G2.Beta))
	b := new(bn256.GT).ScalarMult(pk.eGH, proof.PiF.X())

	c := pk.eGHalphaBeta
	d := bn256.Pair(icPubl, pk.G2.Gamma)
	e := bn256.Pair(proof.PiC, pk.G2.Delta)
	f := bn256.Pair(proof.PiF, proof.PiB)

	ab := new(bn256.GT).Add(a, b)
	cd := new(bn256.GT).Add(c, d)
	ef := new(bn256.GT).Add(e, f)
	cdef := new(bn256.GT).Add(cd, ef)

	if bytes.Equal(ab.Marshal(), cdef.Marshal()) {
		fmt.Println("✓ wolf19 verification passed")
		return true
	}
	return false

}
