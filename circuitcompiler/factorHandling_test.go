package circuitcompiler

import (
	"fmt"
	"github.com/stretchr/testify/assert"
	"math/rand"
	"testing"
)

//factors are essential to identify, if a specific gate has been computed already
//eg. if we can extract a factor from a gate that is independent of commutativity, multiplicativitz we will do much better, in finding and reusing old outputs do
//minimize the multiplication gate number
// for example the gate a*b == gate b*a hence, we only need to compute one of both.

func TestFactorSignature(t *testing.T) {
	facNeutral := factors{&factor{multiplicative: [2]int{1, 1}}}

	//dont let the random number be to big, cuz of overflow
	r1, r2 := rand.Intn(1<<16), rand.Intn(1<<16)
	fmt.Println(r1, r2)
	equalityGroups := [][]factors{
		[]factors{ //test sign and gcd
			{&factor{multiplicative: [2]int{r1 * 2, -r2 * 2}}},
			{&factor{multiplicative: [2]int{-r1, r2}}},
			{&factor{multiplicative: [2]int{r1, -r2}}},
			{&factor{multiplicative: [2]int{r1 * 3, -r2 * 3}}},
			{&factor{multiplicative: [2]int{r1 * r1, -r2 * r1}}},
			{&factor{multiplicative: [2]int{r1 * r2, -r2 * r2}}},
		}, []factors{ //test kommutativity
			{&factor{multiplicative: [2]int{r1, -r2}}, &factor{multiplicative: [2]int{13, 27}}},
			{&factor{multiplicative: [2]int{13, 27}}, &factor{multiplicative: [2]int{-r1, r2}}},
		},
	}

	for _, equalityGroup := range equalityGroups {
		for i := 0; i < len(equalityGroup)-1; i++ {
			sig1, _, _ := factorsSignature(facNeutral, equalityGroup[i])
			sig2, _, _ := factorsSignature(facNeutral, equalityGroup[i+1])
			assert.Equal(t, sig1, sig2)
			sig1, _, _ = factorsSignature(equalityGroup[i], facNeutral)
			sig2, _, _ = factorsSignature(facNeutral, equalityGroup[i+1])
			assert.Equal(t, sig1, sig2)

			sig1, _, _ = factorsSignature(facNeutral, equalityGroup[i])
			sig2, _, _ = factorsSignature(equalityGroup[i+1], facNeutral)
			assert.Equal(t, sig1, sig2)

			sig1, _, _ = factorsSignature(equalityGroup[i], facNeutral)
			sig2, _, _ = factorsSignature(equalityGroup[i+1], facNeutral)
			assert.Equal(t, sig1, sig2)
		}
	}

}

func TestGate_ExtractValues(t *testing.T) {
	facNeutral := factors{&factor{multiplicative: [2]int{8, 7}}, &factor{multiplicative: [2]int{9, 3}}}
	facNeutral2 := factors{&factor{multiplicative: [2]int{9, 1}}, &factor{multiplicative: [2]int{13, 7}}}
	fmt.Println(factorsSignature(facNeutral, facNeutral2))
	f, fc := extractFactor(facNeutral)
	fmt.Println(f)
	fmt.Println(fc)

	f2, _ := extractFactor(facNeutral2)
	fmt.Println(f)
	fmt.Println(fc)
	fmt.Println(factorsSignature(facNeutral, facNeutral2))
	fmt.Println(factorsSignature(f, f2))
}

func TestGCD(t *testing.T) {
	fmt.Println(LCM(10, 15))
	fmt.Println(LCM(10, 15, 20))
	fmt.Println(LCM(1, 2, 3, 4, 5, 6, 7, 8, 9, 10))
}
