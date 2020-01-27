package circuitcompiler

import (
	"fmt"
	"github.com/stretchr/testify/assert"
	"math/big"
	"testing"
)

type InOut struct {
	inputs []*big.Int
	result *big.Int
}

type TraceCorrectnessTest struct {
	skipp bool
	code  string
	io    []InOut
}

var bigNumberResult1, _ = new(big.Int).SetString("2297704271284150716235246193843898764109352875", 10)
var bigNumberResult2, _ = new(big.Int).SetString("75263346540254220740876250", 10)
var pubkeyOf42OnBn256_G1, _ = new(big.Int).SetString("4312786488925573964619847916436127219510912864504589785209181363209026354996", 10)

//NOTE that the results are wrong. need to consider that division is now done on a finite field.
//TODO compute new testcases with a python scrypt
var correctnessTest = []TraceCorrectnessTest{
	{
		skipp: false,
		io: []InOut{{
			inputs: []*big.Int{big.NewInt(int64(3))},
		}},

		code: `
	func main(x){
		var c = x*x
		return x*x
	}
`,
	}, {
		skipp: false,
		io: []InOut{{
			inputs: []*big.Int{pubkeyOf42OnBn256_G1, big.NewInt(int64(42))},
		}},

		code: `
	func main(publicKey, privateKey){
		var pub = scalarBaseMultiply(privateKey)
		equal(pub,publicKey)
	return
}
`,
	},
	{skipp: false,
		io: []InOut{{
			inputs: []*big.Int{big.NewInt(int64(3)), big.NewInt(int64(2)), big.NewInt(328329)},
		}},

		code: `
	func main(x,z,w) {
		if ( (4*7) == 28){
			x=x*x
		}else{
			x=z*z
		}
		var arra[]={x,1,2,3}
		var mul = func(a,b){
			return x*b*7
		}
			var a =1
		var c = w
		
		for( a<3;a=a+1){
			var b = 3
			for( b<4;b=b+2){
				c = mul(c,c)
			}				
		}

		#arra[2]=3
		var k = mul(z,z)
		var l = k*k
		return l*(k*arra[2])*x*x
	}

	func mul(a,b){
	return a*b
	}
	
`,
	}, {skipp: false,
		io: []InOut{{
			inputs: []*big.Int{big.NewInt(int64(7)), big.NewInt(int64(11))},
			result: big.NewInt(int64(2160900)),
		}},

		code: `
	func main( x  ,  z ) {
		if ( 1==2){
			x=x*x
		}else if 3==3{
			x=z*z
		}else{
			x=x*z
		}
		if ( 1==2){
			x=x*x
		}else if 3==3{
			x=x*x
		}else{
			x=x*z
		}
	#	var b = x*x
		
		return
		}		
`,
	},
	{
		skipp: true,
		io: []InOut{{
			inputs: []*big.Int{big.NewInt(int64(7)), big.NewInt(int64(11))},
			result: big.NewInt(int64(2160900)),
		}},

		code: `


	func main( x  ,  z ) {
		var a =1
		var c = 45345146
		for( a<3;a=a+1){
			var b = 3
			#c = foo(x,c)*x
			for( b<4;b=b+2){
				c = foo(x,c)*x
			}	
			
		}
		return
	}	

	func foo(x,y){
		return x*y
	}
	
	func fooX(x,y){
		return x/y
	}`,
	},
	{
		skipp: true,
		io: []InOut{{
			inputs: []*big.Int{big.NewInt(int64(7)), big.NewInt(int64(11))},
			result: big.NewInt(int64(1729500084900343)),
		}, {
			inputs: []*big.Int{big.NewInt(int64(365235)), big.NewInt(int64(11876525))},

			result: bigNumberResult1,
		}},
		code: `
	func main( x  ,  z ) {
		return do(z) + add(x,x)
	}		

	func do(x){
		var e = x * 5
		var b = e * 6
		var c = b * 7
		var F = c * 1
		var d = c * F
		return d * mul(d,e)
	}
	
	func add(x ,k){
		var z = k * x
		return do(x) + mul(x,z)
	}

	func mul(a,b){
		return a * b
	}`,
	},
}

func TestCorrectness(t *testing.T) {

	for _, test := range correctnessTest {

		if test.skipp {
			continue
		}
		//program := newProgram(big.NewInt(int64(5)), big.NewInt(int64(5)))

		program := Parse(test.code, true)

		fmt.Println("\n unreduced")
		fmt.Println(test.code)

		gates := program.ReduceCombinedTree()

		for _, g := range gates {
			fmt.Printf("\n %v", g)
		}

		fmt.Println("\n generating ER1CS")
		r1cs := program.GatesToR1CS(gates)
		fmt.Println(r1cs.L)
		fmt.Println(r1cs.R)
		fmt.Println(r1cs.E)
		fmt.Println(r1cs.O)

		for _, io := range test.io {
			fmt.Println("input")
			fmt.Println(io.inputs)
			inputs := CombineInputs(program.GlobalInputs, io.inputs)
			w, err := CalculateWitness(r1cs, inputs)
			assert.NoError(t, err)
			fmt.Println("witness")
			fmt.Println(w)

		}
	}
}
