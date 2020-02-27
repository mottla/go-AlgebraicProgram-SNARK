package testPrograms

import "math/big"

type InOut struct {
	Inputs []*big.Int
	Result *big.Int
}

type TraceCorrectnessTest struct {
	Skip bool
	Code string
	IO   []InOut
}

var bigNumberResult1, _ = new(big.Int).SetString("2297704271284150716235246193843898764109352875", 10)
var bigNumberResult2, _ = new(big.Int).SetString("75263346540254220740876250", 10)
var pubkeyOf42OnBn256_G1, _ = new(big.Int).SetString("4312786488925573964619847916436127219510912864504589785209181363209026354996", 10)

var TestPrograms = []TraceCorrectnessTest{
	{
		Skip: false,
		IO: []InOut{{
			Inputs: []*big.Int{big.NewInt(int64(3))},
		}},

		Code: `
	var xx = 234515
	
	func main(x){
		var a = func(c,b){
			return (c*c)*b*xx
		}		
		return mul(x,a)
	}

	func mul(a,b){
		return b(a,a)*b(xx,a)
	}
`},
	{
		Skip: true,
		IO: []InOut{{
			Inputs: []*big.Int{big.NewInt(int64(3))},
		}},
		Code: `
	func main(x){
		var a = func(c,b){
			return (c*c)*b
		}
		var c[] = {x, 2*x,a }
		return a(mul(c[0],c[2]),x)
	}

	func mul(a,b){
		return b(a,a)
	}
`,
	}, {
		Skip: false,
		IO: []InOut{{
			Inputs: []*big.Int{pubkeyOf42OnBn256_G1, big.NewInt(int64(42))},
		}},

		Code: `
	func main(publicKey, privateKey){
		var pub = scalarBaseMultiply(privateKey)
		equal(pub,publicKey)
	return
}
`,
	},
	{Skip: false,
		IO: []InOut{{
			Inputs: []*big.Int{big.NewInt(int64(3)), big.NewInt(int64(2)), big.NewInt(328329)},
		}},

		Code: `
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
	}, {Skip: true,
		IO: []InOut{{
			Inputs: []*big.Int{big.NewInt(int64(7)), big.NewInt(int64(11))},
			Result: big.NewInt(int64(2160900)),
		}},

		Code: `
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
		Skip: true,
		IO: []InOut{{
			Inputs: []*big.Int{big.NewInt(int64(7)), big.NewInt(int64(11))},
			Result: big.NewInt(int64(2160900)),
		}},

		Code: `


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
		Skip: true,
		IO: []InOut{{
			Inputs: []*big.Int{big.NewInt(int64(7)), big.NewInt(int64(11))},
			Result: big.NewInt(int64(1729500084900343)),
		}, {
			Inputs: []*big.Int{big.NewInt(int64(365235)), big.NewInt(int64(11876525))},

			Result: bigNumberResult1,
		}},
		Code: `
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