# go-AlgebraicProgram-SNARK
**UNDER CONSTRUCTION**

zkSNARK toolchain for learning purpose. 
Attempt to extend the language from quadratic arithmetic programs to
an algebraic circuit based zkSNARK.
Eg. we use circuits with (+ , - , * , / , g^ ) where g is a generator point of the EC Group G1. 
Theoretic description is in the unfinished ![PDF](algebraicProgramSNARK.pdf).

Note that this scheme is not secure since blind evaluation is restricted to the gates indices rather then to an arbitrary 
point in the underlying finite field, however
somebody might come up with a smart idea how to overcome this issue.
It would be nice, since a shielded transaction (Zcash) would take milliseconds instead of seconds!

**Circuit Language**
This toolchain comes along with a compiler fully written in go.
Currently supported:
- if-else support for static expressions
- static for loops
- declare function inside functions via: var foo = func(..){..}; call with: foo(args...)
- declare multiple functions via:
 func identifier (arguments...){...}
- declare variable: var x = expression
- variable overloading: x = expression
- array declaration: var k[]={expression,expression,..}
- equality check. call equal(a,b), to ensure that a is equal to b at a given point of code execution.
 use this to verify signatures etc.
 - scalarBaseMultiply(x): to perform a point multiplication on the source group with just one gate. If its never called we have a normal zkSNARK toolchain.

This language then gets compiled into a R1CS form, with focus on gate reduction.
We reuse gates whenever possible, exploit commutative properties of the gates, extract constant factors as long as possible etc.

**Example of extended algebraic program SNARK**

the predefined function *scalarBaseMultiply(a)* performs a point multiplication on
the elliptic curve that defines the the source group G1 of the BN256 pairing implementation and returns
the points x coordinate.
Loosely speaking: With this we can prove knowledge of a privateKey in just one gate, instead of approx. 1000, as in classic implementations
```
#if we trun this code to a snark, the privatekey argument will not be part of the public statement naturaly.
func main(publicKey, privateKey){
    #var pub = x <- (x,y) <- g^private , where g is generator of G1 of BN256
    var pub = scalarBaseMultiply(privateKey)
    #create a constraint that can only be satisfied if the input publicKey is equal to the computed value pub 
    equal(pub,publicKey)
    return
}
```
The EAP then has the form:
```
[[0 0 0 0] [0 0 0 1]]
[[0 0 0 0] [1 0 0 0]]
[[0 0 1 0] [0 0 0 0]]
[[0 0 0 1] [0 1 0 0]]
```
when we pick the input s.t. publicKey = X(g^42) we get
[publicKey=4312786488925573964619847916436127219510912864504589785209181363209026354996 privateKey=42]
and the witness trace
[1 4312786488925573964619847916436127219510912864504589785209181363209026354996 42 4312786488925573964619847916436127219510912864504589785209181363209026354996]

**Example of classic SNARK** (without the extention explained in the ![PDF](algebraicProgramSNARK.pdf))

```
func main(x,z,w) {
    #this is a comment
    if ( (4*7) == 28){
        x=x*x
    }else{
        x=z*z
    }

    var arra[]={x,1,2,3}

    #functions can be declared within functions. therby we overload outside scope
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
```
R1SC form of the code above. 
Note that the big number at the end is because we do arithmetic on a finite field and we extract factors as long as possible to reduce gates.
so inverses and negative numbers are likely huge.
The R1CS of the code above:
```
[[0 0 0 1 0 0 0 0 0 0 0 0] [0 1 0 0 0 0 0 0 0 0 0 0] [0 0 0 0 1 0 0 0 0 0 0 0] [0 0 1 0 0 0 0 0 0 0 0 0] [0 0 0 0 0 1 0 0 0 0 0 0] [0 0 0 0 0 0 0 1 0 0 0 0] [0 0 0 0 0 0 0 1 0 0 0 0] [0 0 0 0 0 0 0 0 0 1 0 0]]
[[0 0 0 1 0 0 0 0 0 0 0 0] [0 1 0 0 0 0 0 0 0 0 0 0] [0 0 0 0 0 1 0 0 0 0 0 0] [0 0 0 0 0 1 0 0 0 0 0 0] [0 0 0 0 0 1 0 0 0 0 0 0] [0 0 0 0 0 0 0 0 1 0 0 0] [0 0 0 0 0 0 0 1 0 0 0 0] [0 0 0 0 0 0 0 0 0 0 1 0]]
[[0 0 0 0 1 0 0 0 0 0 0 0] [0 0 0 0 0 1 0 0 0 0 0 0] [0 0 0 0 0 0 3126891838834182174606629392179610726935480628630862049099743455225115499374 0 0 0 0 0] [0 0 0 0 0 0 0 1 0 0 0 0] [0 0 0 0 0 0 0 0 1 0 0 0] [0 0 0 0 0 0 0 0 0 1 0 0] [0 0 0 0 0 0 0 0 0 0 1 0] [0 0 0 0 0 0 0 0 0 0 0 10752679078439993804514633726168661377318948692332658270883811677661876768255]]

```
Calculate the witness given the R1CS 
input

[x=3 z=2 w=328329]

gives witness witness

[1 x=3 z=2 w=328329 107799932241 9 6791395731183 18 81 1458 324 324060912]

