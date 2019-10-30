package zkSNARK

import (
	"bytes"
	"fmt"
	"github.com/mottla/go-AlgebraicProgram-SNARK/circuitcompiler"
	bn256 "github.com/mottla/go-AlgebraicProgram-SNARK/circuitcompiler/pairing"

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
func CombinePolynomials(fields circuitcompiler.Fields, witness []*big.Int, TransposedR1cs circuitcompiler.ER1CS) (Gx, Px []*big.Int) {

	pf := fields.PF

	scalarProduct := func(vec [][]*big.Int) (poly []*big.Int) {
		var ax []*big.Int
		for i := 0; i < len(witness); i++ {
			m := pf.Mul([]*big.Int{witness[i]}, vec[i])
			ax = pf.Add(ax, m)
		}
		return ax
	}

	LVec := pf.LagrangeInterpolation(scalarProduct(TransposedR1cs.L))
	RVec := pf.LagrangeInterpolation(scalarProduct(TransposedR1cs.R))
	fmt.Println(TransposedR1cs.R)
	fmt.Println(scalarProduct(TransposedR1cs.R))
	fmt.Println(RVec)
	fmt.Println(pf.Eval(RVec, new(big.Int).SetInt64(1)))
	fmt.Println(pf.Eval(RVec, new(big.Int).SetInt64(2)))
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
func g1ScalarBaseMultiply(in *big.Int) *bn256.G1 {
	return new(bn256.G1).ScalarBaseMult(in)
}
func g2ScalarBaseMultiply(in *big.Int) *bn256.G2 {
	return new(bn256.G2).ScalarBaseMult(in)
}

// GenerateTrustedSetup generates the Trusted Setup from a compiled Circuit. The Setup.Toxic sub data structure must be destroyed
func GenerateTrustedSetup(fields circuitcompiler.Fields, witnessLength, gates, publicinputs int, Li, Ri, Ei, Oi [][]*big.Int) (Setup, error) {
	var setup Setup
	var err error

	// generate random t value
	setup.Toxic.x, err = fields.FqR.Rand()
	if err != nil {
		return Setup{}, err
	}
	//setup.Toxic.x = new(big.Int).SetInt64(1)

	setup.Toxic.Kalpha, err = fields.FqR.Rand()
	if err != nil {
		return Setup{}, err
	}
	setup.Toxic.Kbeta, err = fields.FqR.Rand()
	if err != nil {
		return Setup{}, err
	}
	setup.Toxic.Kgamma, err = fields.FqR.Rand()
	if err != nil {
		return Setup{}, err
	}
	setup.Toxic.Kdelta, err = fields.FqR.Rand()
	if err != nil {
		return Setup{}, err
	}

	//generate the domain polynomial
	Domain := []*big.Int{big.NewInt(int64(1))}

	//(x)(x-1)(x-2)..
	for i := 0; i < gates; i++ {
		Domain = fields.PF.Mul(
			Domain,
			[]*big.Int{
				fields.FqR.Neg(big.NewInt(int64(i))), big.NewInt(int64(1)),
			})
	}
	y := []*big.Int{}
	for i := 0; i < gates; i++ {
		y = append(y, new(big.Int).SetInt64(0))
	}
	test := fields.PF.LagrangeInterpolation(y)
	fmt.Println(test)
	setup.Pk.Domain = Domain
	Dx := fields.PF.Eval(Domain, setup.Toxic.x)
	invDelta := fields.FqR.Inverse(setup.Toxic.Kdelta)
	Dx_div_delta := fields.FqR.Mul(invDelta, Dx)

	// encrypt x values with curve generators
	// x^i times D(x) divided by delta
	var powersXDomaindivDelta []*bn256.G1
	var powersX_onG []*bn256.G1
	var powersX_onH []*bn256.G2
	ini := g1ScalarBaseMultiply(Dx_div_delta)

	//G^{x^i}
	powersX_onG = append(powersX_onG, g1ScalarBaseMultiply(new(big.Int).SetInt64(1)))
	powersXDomaindivDelta = append(powersXDomaindivDelta, ini)
	tEncr := setup.Toxic.x
	for i := 1; i < len(Ri); i++ {
		powersXDomaindivDelta = append(powersXDomaindivDelta, g1ScalarBaseMultiply(fields.FqR.Mul(tEncr, Dx_div_delta)))
		powersX_onG = append(powersX_onG, g1ScalarBaseMultiply(tEncr))
		powersX_onH = append(powersX_onH, g2ScalarBaseMultiply(tEncr))
		// x^i -> x^{i+1}
		tEncr = fields.FqR.Mul(tEncr, setup.Toxic.x)
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
		// G^Lix
		lix := fields.PF.Eval(Li[i], setup.Toxic.x)

		// G^Rix
		grix := fields.PF.Eval(Ri[i], setup.Toxic.x)

		// G^Oix
		oix := fields.PF.Eval(Oi[i], setup.Toxic.x)

		// G^Eix
		eix := fields.PF.Eval(Ei[i], setup.Toxic.x)
		setup.Pk.G1.Ex = append(setup.Pk.G1.Ex, g1ScalarBaseMultiply(eix))

		setup.Pk.G1.Lx_plus_Ex = append(setup.Pk.G1.Lx_plus_Ex, g1ScalarBaseMultiply(fields.FqR.Add(eix, lix)))

		//H^Rix
		hrix := fields.PF.Eval(Ri[i], setup.Toxic.x)
		hRix := g2ScalarBaseMultiply(hrix)
		setup.Pk.G2.Rx = append(setup.Pk.G2.Rx, hRix)

		ter := fields.FqR.Mul(setup.Toxic.Kalpha, grix)
		ter = fields.FqR.Add(ter, fields.FqR.Mul(setup.Toxic.Kbeta, lix))
		ter = fields.FqR.Add(ter, fields.FqR.Mul(setup.Toxic.Kbeta, eix))
		ter = fields.FqR.Add(ter, oix)

		if i <= publicinputs {
			invgamma := fields.FqR.Inverse(setup.Toxic.Kgamma)
			ter = fields.FqR.Mul(invgamma, ter)
			setup.Pk.G1.RLEO_Gamma = append(setup.Pk.G1.RLEO_Gamma, g1ScalarBaseMultiply(ter))
		} else {
			invdelta := fields.FqR.Inverse(setup.Toxic.Kdelta)
			ter = fields.FqR.Mul(invdelta, ter)
			setup.Pk.G1.RLEO_Delta = append(setup.Pk.G1.RLEO_Delta, g1ScalarBaseMultiply(ter))
		}
	}
	setup.Pk.eGH = bn256.Pair(g1ScalarBaseMultiply(new(big.Int).SetInt64(1)), g2ScalarBaseMultiply(new(big.Int).SetInt64(1)))
	setup.Pk.eGHalphaBeta = new(bn256.GT).ScalarMult(setup.Pk.eGH, fields.FqR.Mul(setup.Toxic.Kalpha, setup.Toxic.Kbeta))
	return setup, nil
}

// GenerateProofs generates all the parameters to proof the zkSNARK from the Circuit, Setup and the Witness
func GenerateProofs(fields circuitcompiler.Fields, witnessLength, publicinputs int, pk Pk, w []*big.Int, Px []*big.Int) (Proof, error) {
	var proof Proof
	proof.PiA = new(bn256.G1).ScalarMult(pk.G1.Lx_plus_Ex[0], w[0])
	proof.PiB = new(bn256.G2).ScalarMult(pk.G2.Rx[0], w[0])
	proof.PiC = new(bn256.G1).ScalarMult(pk.G1.RLEO_Delta[0], w[publicinputs+1])
	proof.PiF = new(bn256.G1).ScalarMult(pk.G1.Ex[0], w[0])

	var QxDx_div_delta = new(bn256.G1)
	Qx, _ := fields.PF.Div(Px, pk.Domain)

	for i, QxCoefficient := range Qx {
		tmp := new(bn256.G1).ScalarMult(pk.G1.PowersX_Domain_Delta[i], QxCoefficient)
		QxDx_div_delta.Add(QxDx_div_delta, tmp)
	}

	for i := 1; i < witnessLength; i++ {
		//proof element A
		proof.PiA.Add(proof.PiA, new(bn256.G1).ScalarMult(pk.G1.Lx_plus_Ex[i], w[i]))

		//proof element B
		proof.PiB.Add(proof.PiB, new(bn256.G2).ScalarMult(pk.G2.Rx[i], w[i]))

		if i > publicinputs+1 {
			//proof element C
			proof.PiC.Add(proof.PiC, new(bn256.G1).ScalarMult(pk.G1.RLEO_Delta[i-publicinputs-1], w[i]))
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

// VerifyProof verifies over the BN128 the Pairings of the Proof
func VerifyProof(pk Pk, proof Proof, publicSignals []*big.Int, debug bool) bool {
	//note that the trivial cases should be rejected to

	if len(publicSignals) != len(pk.G1.RLEO_Gamma) {
		fmt.Println("❌ wolf19 verification not passed. Signal length wrong")
		return false
	}

	icPubl := new(bn256.G1).ScalarMult(pk.G1.RLEO_Gamma[0], publicSignals[0])
	for i := 1; i < len(publicSignals); i++ {
		icPubl.Add(icPubl, new(bn256.G1).ScalarMult(pk.G1.RLEO_Gamma[i], publicSignals[i]))
	}
	if bytes.Equal(
		new(bn256.GT).Add(
			bn256.Pair(proof.PiA, proof.PiB), new(bn256.GT).ScalarMult(pk.eGH, proof.PiF.X())).Marshal(),
		new(bn256.GT).Add(
			pk.eGHalphaBeta, new(bn256.GT).Add(
				bn256.Pair(icPubl, pk.G2.Gamma), new(bn256.GT).Add(
					bn256.Pair(proof.PiC, pk.G2.Delta), bn256.Pair(proof.PiF, proof.PiB)))).Marshal()) {
		fmt.Println("✓ wolf19 verification passed")
		return true
	}
	return false

}
