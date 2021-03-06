package zkSNARK

import (
	"bytes"
	"fmt"
	"github.com/mottla/go-AlgebraicProgram-SNARK/circuitcompiler"
	bn256 "github.com/mottla/go-AlgebraicProgram-SNARK/pairing"
	"github.com/mottla/go-AlgebraicProgram-SNARK/utils"
	"math/big"
	"time"
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
func CombinePolynomials2(witness []*big.Int, TransposedR1cs *circuitcompiler.ER1CSTransposed) (Px []*big.Int) {

	pf := utils.Field.PolynomialField

	//note thate we could first multiply, add and sub with the datapoints and then interpolate.
	//however after the multiplication, the degree is higher. interpolation time is
	//quadratic to the degree. Therefor its more efficient to interpolate and then operate.
	//however.. the datapoints are sparse. if i interpolate them. they wont be sparse any longer
	//multiplication takes full square time.
	//most efficient is therfor precomputing lagrange bases, interpolate and then perform the operations.
	LVec := pf.LagrangeInterpolation(pf.AddPolynomials(pf.LinearCombine(TransposedR1cs.L, witness)))
	RVec := pf.LagrangeInterpolation(pf.AddPolynomials(pf.LinearCombine(TransposedR1cs.R, witness)))
	EVec := pf.AddPolynomials(pf.LinearCombine(TransposedR1cs.E, witness))
	OVec := pf.LagrangeInterpolation(pf.AddPolynomials(pf.LinearCombine(TransposedR1cs.O, witness)))

	var mG_pointsVec []*big.Int
	for i := 0; i < len(EVec); i++ {
		p := g1ScalarBaseMultiply(EVec[i])
		mG_pointsVec = append(mG_pointsVec, p.X())
	}
	Gx := pf.LagrangeInterpolation(mG_pointsVec)
	a := pf.Mul(LVec, RVec)
	b := pf.Add(a, Gx)
	c := pf.Sub(b, OVec)
	return c
}

//CombinePolynomials combine the given polynomials arrays into one, also returns the P(x)
func CombineSparsePolynomials(witness []*big.Int, TransposedR1cs *circuitcompiler.ER1CSsPARSETransposed) (Px *utils.AvlTree) {

	pf := utils.Field.ArithmeticField

	scalarProduct := func(vec []*utils.AvlTree) (poly *utils.AvlTree) {
		poly = pf.AddPolynomials(pf.LinearCombine(vec, witness))
		return
	}

	LVec := pf.InterpolateSparseArray(scalarProduct(TransposedR1cs.L), TransposedR1cs.NumberOfGates)
	RVec := pf.InterpolateSparseArray(scalarProduct(TransposedR1cs.R), TransposedR1cs.NumberOfGates)
	EVec := scalarProduct(TransposedR1cs.E)
	OVec := pf.InterpolateSparseArray(scalarProduct(TransposedR1cs.O), TransposedR1cs.NumberOfGates)

	var mG_pointsVec = utils.NewAvlTree()
	for v := range EVec.ChannelNodes(true) {
		p := g1ScalarBaseMultiply(v.Value)
		mG_pointsVec.InsertNoOverwriteAllowed(v.Key, p.X())
	}
	Gx := pf.InterpolateSparseArray(mG_pointsVec, TransposedR1cs.NumberOfGates)
	Px = pf.MulSparse(LVec, RVec)
	Px = pf.AddToSparse(Px, Gx)
	Px = pf.SubToSparse(Px, OVec)
	return
}

func g1ScalarBaseMultiply(in *big.Int) *bn256.G1 {
	return new(bn256.G1).ScalarBaseMult(in)
}
func g2ScalarBaseMultiply(in *big.Int) *bn256.G2 {
	return new(bn256.G2).ScalarBaseMult(in)
}

// GenerateTrustedSetup generates the Trusted Setup from a compiled function. The Setup.Toxic sub data structure must be destroyed
func GenerateTrustedSetup(publicinputs int, r1cs *circuitcompiler.ER1CSTransposed) (*Setup, error) {
	gates, witnessLength := r1cs.NumberOfGates, r1cs.WitnessLength

	//this bastard is heavy to compute. we interpolate all the polynomials
	fmt.Println("start interpolation...")
	before := time.Now()
	Li, Ri, Ei, Oi := r1cs.ER1CSToEAP()
	fmt.Println("interpolation done in ", time.Since(before))
	if len(Li) != len(Ri) || len(Ri) != len(Ei) || len(Ei) != len(Oi) {
		panic("amount of polynimials  missmatch")
	}
	if publicinputs >= len(Li) {
		panic("to moany public parameters")
	}

	var setup = new(Setup)
	var err error
	fields := utils.Field
	// generate random t value
	setup.Toxic.x, err = fields.ArithmeticField.Rand()
	if err != nil {
		panic("random failed")
	}
	//TODO this is why my scheme sucks. we can only have x in {0,..,len(gates)} and not from the entire field. This destroys security
	//setup.Toxic.x = big.NewInt(rand.Int63n(int64(gates)))

	setup.Toxic.Kalpha, err = fields.ArithmeticField.Rand()
	if err != nil {
		panic("random failed")
	}
	setup.Toxic.Kbeta, err = fields.ArithmeticField.Rand()
	if err != nil {
		panic("random failed")
	}
	setup.Toxic.Kgamma, err = fields.ArithmeticField.Rand()
	if err != nil {
		panic("random failed")
	}
	setup.Toxic.Kdelta, err = fields.ArithmeticField.Rand()
	if err != nil {
		panic("random failed")
	}

	//generate the domain polynomial
	Domain := fields.PolynomialField.DomainPolynomial(gates)

	setup.Pk.Domain = Domain
	//TODO other field maybe??
	Dx := fields.ArithmeticField.EvalPoly(Domain, setup.Toxic.x)
	invDelta := fields.ArithmeticField.Inverse(setup.Toxic.Kdelta)
	invgamma := fields.ArithmeticField.Inverse(setup.Toxic.Kgamma)
	Dx_div_delta := fields.ArithmeticField.Mul(invDelta, Dx)

	// encrypt x values with curve generators
	// x^i times D(x) divided by delta
	var powersXDomaindivDelta = []*bn256.G1{g1ScalarBaseMultiply(Dx_div_delta)}
	var powersX_onG = []*bn256.G1{g1ScalarBaseMultiply(big.NewInt(1))}
	var powersX_onH = []*bn256.G2{g2ScalarBaseMultiply(big.NewInt(1))}

	//G^{x^i}
	tEncr := new(big.Int).Set(setup.Toxic.x)
	for i := 1; i < gates; i++ {
		powersXDomaindivDelta = append(powersXDomaindivDelta, g1ScalarBaseMultiply(fields.ArithmeticField.Mul(tEncr, Dx_div_delta)))
		powersX_onG = append(powersX_onG, g1ScalarBaseMultiply(tEncr))
		powersX_onH = append(powersX_onH, g2ScalarBaseMultiply(tEncr))
		// x^i -> x^{i+1}
		tEncr = fields.ArithmeticField.Mul(tEncr, setup.Toxic.x)
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
		// Li(x)
		lix := fields.ArithmeticField.EvalPoly(Li[i], setup.Toxic.x)
		// Ri(x)
		rix := fields.ArithmeticField.EvalPoly(Ri[i], setup.Toxic.x)
		// Oi(x)
		oix := fields.ArithmeticField.EvalPoly(Oi[i], setup.Toxic.x)

		// Ei(x)
		eix := fields.ArithmeticField.EvalPoly(Ei[i], setup.Toxic.x)
		setup.Pk.G1.Ex = append(setup.Pk.G1.Ex, g1ScalarBaseMultiply(eix))

		setup.Pk.G1.Lx_plus_Ex = append(setup.Pk.G1.Lx_plus_Ex, g1ScalarBaseMultiply(fields.ArithmeticField.Add(eix, lix)))

		//H^Rix
		hRix := g2ScalarBaseMultiply(fields.ArithmeticField.Copy(rix))
		setup.Pk.G2.Rx = append(setup.Pk.G2.Rx, hRix)

		ter := fields.ArithmeticField.Mul(setup.Toxic.Kalpha, rix)
		ter = fields.ArithmeticField.Add(ter, fields.ArithmeticField.Mul(setup.Toxic.Kbeta, lix))
		ter = fields.ArithmeticField.Add(ter, fields.ArithmeticField.Mul(setup.Toxic.Kbeta, eix))
		ter = fields.ArithmeticField.Add(ter, oix)

		if i < publicinputs {
			ter = fields.ArithmeticField.Mul(invgamma, ter)
			setup.Pk.G1.RLEO_Gamma = append(setup.Pk.G1.RLEO_Gamma, g1ScalarBaseMultiply(ter))
		} else {
			ter = fields.ArithmeticField.Mul(invDelta, ter)
			setup.Pk.G1.RLEO_Delta = append(setup.Pk.G1.RLEO_Delta, g1ScalarBaseMultiply(ter))
		}
	}
	setup.Pk.eGH = bn256.Pair(g1ScalarBaseMultiply(new(big.Int).SetInt64(1)), g2ScalarBaseMultiply(new(big.Int).SetInt64(1)))
	//is a field multiplication under order g1 wrong?
	setup.Pk.eGHalphaBeta = bn256.Pair(g1ScalarBaseMultiply(setup.Toxic.Kalpha), g2ScalarBaseMultiply(setup.Toxic.Kbeta))
	return setup, nil
}

// GenerateTrustedSetup generates the Trusted Setup from a compiled function. The Setup.Toxic sub data structure must be destroyed
func GenerateTrustedSetupSparse(publicinputs int, in *circuitcompiler.ER1CSsPARSETransposed) (*Setup, error) {
	gates, witnessLength := in.NumberOfGates, in.WitnessLength
	fmt.Println("start interpolation...")
	before := time.Now()
	Li, Ri, Ei, Oi := in.ER1CSToEAPSparse()
	fmt.Println("interpolation done in ", time.Since(before))
	if len(Li) != len(Ri) || len(Ri) != len(Ei) || len(Ei) != len(Oi) {
		panic("amount of polynimials  missmatch")
	}
	if publicinputs >= len(Li) {
		panic("to moany public parameters")
	}

	var setup = new(Setup)
	var err error
	fields := utils.Field
	// generate random t value
	setup.Toxic.x, err = fields.ArithmeticField.Rand()
	if err != nil {
		panic("random failed")
	}
	//TODO this is why my scheme sucks. we can only have x in {0,..,len(gates)} and not from the entire field. This destroys security
	//setup.Toxic.x = big.NewInt(rand.Int63n(int64(gates)))

	setup.Toxic.Kalpha, err = fields.ArithmeticField.Rand()
	if err != nil {
		panic("random failed")
	}
	setup.Toxic.Kbeta, err = fields.ArithmeticField.Rand()
	if err != nil {
		panic("random failed")
	}
	setup.Toxic.Kgamma, err = fields.ArithmeticField.Rand()
	if err != nil {
		panic("random failed")
	}
	setup.Toxic.Kdelta, err = fields.ArithmeticField.Rand()
	if err != nil {
		panic("random failed")
	}

	//generate the domain polynomial
	Domain := fields.PolynomialField.DomainPolynomial(gates)

	setup.Pk.Domain = Domain
	//TODO other field maybe??
	Dx := fields.ArithmeticField.EvalPoly(Domain, setup.Toxic.x)
	invDelta := fields.ArithmeticField.Inverse(setup.Toxic.Kdelta)
	invgamma := fields.ArithmeticField.Inverse(setup.Toxic.Kgamma)
	Dx_div_delta := fields.ArithmeticField.Mul(invDelta, Dx)

	// encrypt x values with curve generators
	// x^i times D(x) divided by delta
	var powersXDomaindivDelta = []*bn256.G1{g1ScalarBaseMultiply(Dx_div_delta)}
	var powersX_onG = []*bn256.G1{g1ScalarBaseMultiply(big.NewInt(1))}
	var powersX_onH = []*bn256.G2{g2ScalarBaseMultiply(big.NewInt(1))}

	//G^{x^i}
	tEncr := new(big.Int).Set(setup.Toxic.x)
	for i := 1; i < gates; i++ {
		powersXDomaindivDelta = append(powersXDomaindivDelta, g1ScalarBaseMultiply(fields.ArithmeticField.Mul(tEncr, Dx_div_delta)))
		powersX_onG = append(powersX_onG, g1ScalarBaseMultiply(tEncr))
		powersX_onH = append(powersX_onH, g2ScalarBaseMultiply(tEncr))
		// x^i -> x^{i+1}
		tEncr = fields.ArithmeticField.Mul(tEncr, setup.Toxic.x)
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
		// Li(x)
		lix := fields.ArithmeticField.EvalSparsePoly(Li[i], setup.Toxic.x)
		// Ri(x)
		rix := fields.ArithmeticField.EvalSparsePoly(Ri[i], setup.Toxic.x)
		// Oi(x)
		oix := fields.ArithmeticField.EvalSparsePoly(Oi[i], setup.Toxic.x)

		// Ei(x)
		eix := fields.ArithmeticField.EvalSparsePoly(Ei[i], setup.Toxic.x)
		setup.Pk.G1.Ex = append(setup.Pk.G1.Ex, g1ScalarBaseMultiply(eix))

		setup.Pk.G1.Lx_plus_Ex = append(setup.Pk.G1.Lx_plus_Ex, g1ScalarBaseMultiply(fields.ArithmeticField.Add(eix, lix)))

		//H^Rix
		hRix := g2ScalarBaseMultiply(fields.ArithmeticField.Copy(rix))
		setup.Pk.G2.Rx = append(setup.Pk.G2.Rx, hRix)

		ter := fields.ArithmeticField.Mul(setup.Toxic.Kalpha, rix)
		ter = fields.ArithmeticField.Add(ter, fields.ArithmeticField.Mul(setup.Toxic.Kbeta, lix))
		ter = fields.ArithmeticField.Add(ter, fields.ArithmeticField.Mul(setup.Toxic.Kbeta, eix))
		ter = fields.ArithmeticField.Add(ter, oix)

		if i < publicinputs {
			ter = fields.ArithmeticField.Mul(invgamma, ter)
			setup.Pk.G1.RLEO_Gamma = append(setup.Pk.G1.RLEO_Gamma, g1ScalarBaseMultiply(ter))
		} else {
			ter = fields.ArithmeticField.Mul(invDelta, ter)
			setup.Pk.G1.RLEO_Delta = append(setup.Pk.G1.RLEO_Delta, g1ScalarBaseMultiply(ter))
		}
	}
	setup.Pk.eGH = bn256.Pair(g1ScalarBaseMultiply(new(big.Int).SetInt64(1)), g2ScalarBaseMultiply(new(big.Int).SetInt64(1)))
	//is a field multiplication under order g1 wrong?
	setup.Pk.eGHalphaBeta = bn256.Pair(g1ScalarBaseMultiply(setup.Toxic.Kalpha), g2ScalarBaseMultiply(setup.Toxic.Kbeta))
	return setup, nil
}

// GenerateProofs generates all the parameters to proof the zkSNARK from the function, Setup and the Witness
func GenerateProofs(publicInputs int, provingKey *Pk, witnessTrace []*big.Int, Px []*big.Int) (*Proof, error) {
	var proof = new(Proof)
	f := utils.Field

	proof.PiA = new(bn256.G1).ScalarMult(provingKey.G1.Lx_plus_Ex[0], witnessTrace[0])
	proof.PiB = new(bn256.G2).ScalarMult(provingKey.G2.Rx[0], witnessTrace[0])
	proof.PiC = new(bn256.G1).ScalarMult(provingKey.G1.RLEO_Delta[0], witnessTrace[publicInputs])
	proof.PiF = new(bn256.G1).ScalarMult(provingKey.G1.Ex[0], witnessTrace[0])
	Qx, r := f.PolynomialField.Div(Px, provingKey.Domain)

	if !utils.IsZeroArray(r) {
		panic("remainder supposed to be 0")
	}

	var QxDx_div_delta = new(bn256.G1).ScalarMult(provingKey.G1.PowersX_Domain_Delta[0], Qx[0])

	for i := 1; i < len(Qx); i++ {
		tmp := new(bn256.G1).ScalarMult(provingKey.G1.PowersX_Domain_Delta[i], Qx[i])
		QxDx_div_delta.Add(QxDx_div_delta, tmp)
	}

	for i := 1; i < len(witnessTrace); i++ {
		//proof element A
		proof.PiA.Add(proof.PiA, new(bn256.G1).ScalarMult(provingKey.G1.Lx_plus_Ex[i], witnessTrace[i]))

		//proof element B
		proof.PiB.Add(proof.PiB, new(bn256.G2).ScalarMult(provingKey.G2.Rx[i], witnessTrace[i]))

		if i > publicInputs {
			//proof element C
			proof.PiC.Add(proof.PiC, new(bn256.G1).ScalarMult(provingKey.G1.RLEO_Delta[i-publicInputs], witnessTrace[i]))
		}
		//proof element F
		proof.PiF.Add(proof.PiF, new(bn256.G1).ScalarMult(provingKey.G1.Ex[i], witnessTrace[i]))
	}
	//add the alpha therm to proof element A
	proof.PiA.Add(proof.PiA, provingKey.G1.Alpha)

	//add the Q(x)D(x)/delta therm to the proof element C
	proof.PiC.Add(proof.PiC, QxDx_div_delta)

	return proof, nil
}

// GenerateProofs generates all the parameters to proof the zkSNARK from the function, Setup and the Witness
func GenerateProof_Sparse(publicInputs int, provingKey *Pk, witnessTrace []*big.Int, Px *utils.AvlTree) (*Proof, error) {
	var proof = new(Proof)
	f := utils.Field

	proof.PiA = new(bn256.G1).ScalarMult(provingKey.G1.Lx_plus_Ex[0], witnessTrace[0])
	proof.PiB = new(bn256.G2).ScalarMult(provingKey.G2.Rx[0], witnessTrace[0])
	proof.PiC = new(bn256.G1).ScalarMult(provingKey.G1.RLEO_Delta[0], witnessTrace[publicInputs])
	proof.PiF = new(bn256.G1).ScalarMult(provingKey.G1.Ex[0], witnessTrace[0])
	Qx, r := f.ArithmeticField.DivideSparse(Px, utils.NewSparseArrayFromArray(provingKey.Domain))

	if r.Size() > 0 {
		panic("remainder supposed to be 0")
	}

	var QxDx_div_delta = g1ScalarBaseMultiply(big.NewInt(0))

	for L := range Qx.ChannelNodes(true) {
		tmp := new(bn256.G1).ScalarMult(provingKey.G1.PowersX_Domain_Delta[L.Key], L.Value)
		QxDx_div_delta.Add(QxDx_div_delta, tmp)
	}

	for i := 1; i < len(witnessTrace); i++ {
		//proof element A
		proof.PiA.Add(proof.PiA, new(bn256.G1).ScalarMult(provingKey.G1.Lx_plus_Ex[i], witnessTrace[i]))

		//proof element B
		proof.PiB.Add(proof.PiB, new(bn256.G2).ScalarMult(provingKey.G2.Rx[i], witnessTrace[i]))

		if i > publicInputs {
			//proof element C
			proof.PiC.Add(proof.PiC, new(bn256.G1).ScalarMult(provingKey.G1.RLEO_Delta[i-publicInputs], witnessTrace[i]))
		}
		//proof element F
		proof.PiF.Add(proof.PiF, new(bn256.G1).ScalarMult(provingKey.G1.Ex[i], witnessTrace[i]))
	}
	//add the alpha therm to proof element A
	proof.PiA.Add(proof.PiA, provingKey.G1.Alpha)

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
	fmt.Println("❌ wolf19 verification not passed.")
	return false

}
