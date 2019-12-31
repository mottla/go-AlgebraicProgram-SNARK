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

//NOTE that the results are wrong. need to consider that division is now done on a finite field.
//TODO compute new testcases with a python scrypt
var correctnessTest = []TraceCorrectnessTest{
	{skipp: false,
		io: []InOut{{
			inputs: []*big.Int{big.NewInt(int64(3)), big.NewInt(int64(2)), big.NewInt(328329)},
		}},

		code: `
	def main(x,z,w) {
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

	def mul(a,b){
	return a*b
	}
	
`,
	}, {skipp: false,
		io: []InOut{{
			inputs: []*big.Int{big.NewInt(int64(7)), big.NewInt(int64(11))},
			result: big.NewInt(int64(2160900)),
		}},

		code: `
	def main( x  ,  z ) {
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
		skipp: false,
		io: []InOut{{
			inputs: []*big.Int{big.NewInt(int64(7)), big.NewInt(int64(11))},
			result: big.NewInt(int64(2160900)),
		}},

		code: `


	def main( x  ,  z ) {
		var a =1
		var c = 45345146
		for( a<3;a=a+1){
			var b = 3
			for( b<4;b=b+2){
				c = foo(x,c)*x
			}	
			
		}
		return
	}	

	def foo(x,y){
		return x*y
	}
	
	def fooX(x,y){
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
	def main( x  ,  z ) {
		return do(z) + add(x,x)
	}		

	def do(x){
		var e = x * 5
		var b = e * 6
		var c = b * 7
		var f = c * 1
		var d = c * f
		return d * mul(d,e)
	}
	
	def add(x ,k){
		var z = k * x
		return do(x) + mul(x,z)
	}

	def mul(a,b){
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
			inputs := io.inputs
			fmt.Println("input")
			fmt.Println(inputs)
			w, err := r1cs.CalculateWitness(inputs, program.Fields)
			assert.NoError(t, err)
			fmt.Println("witness")
			fmt.Println(w)

		}
	}
}
