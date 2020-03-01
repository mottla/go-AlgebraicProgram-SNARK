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
My goal was, to create a compiler for a language that is as close to golang as possible.
The language is fully functional. Functions and field elements are the only first class citizen e.g.
functions can be passed as arguments (see example).
Due to the nature of zkSNARKs some things such as dynamic looping, parallelism, dynamic array access cannot be supported.

Additionaly we support some supported some arithmetic circuit specific functions:
- equality check. call equal(a,b), to ensure that a is equal to b at a given point of code execution.
 use this to verify signatures etc.
 - scalarBaseMultiply(x): to perform a point multiplication on the source group with just one gate. If its never called we have a normal zkSNARK toolchain.

This language then gets compiled into a R1CS form, with focus on gate reduction.
We reuse gates whenever possible, exploit commutative properties of the gates, extract constant factors as long as possible etc.

**Example of classic SNARK** (without the extension explained in the ![PDF](algebraicProgramSNARK.pdf))

```
#comment
#every programm need a main with arbitrarily many field elements as arguments
func main(x){
   
    #functions can be declared within functions
    var a = func(i){
        if i == 0 {
            return
        }
        i = i-1
        return x*a(i)			
    }
    
    var b = 7
    var c = 123 * b    
    return mul(1/c,a(array[3]*2))
}

var xx = 4
var array[] = {1,4,7,xx}

func mul(a,b){
    return a*b
}
```
R1SC form of the code above (last constraint and last two witnesses are due to randomization. Not needed if Jenns Groths scheme is applied):

```
[[0 1 0 0 0 0 0 0 0 0 0] [0 0 1 0 0 0 0 0 0 0 0] [0 0 0 1 0 0 0 0 0 0 0] [0 0 0 0 1 0 0 0 0 0 0] [0 0 0 0 0 1 0 0 0 0 0] [0 0 0 0 0 0 1 0 0 0 0] [0 0 0 0 0 0 0 1 0 0 0] [0 0 0 0 0 0 0 0 0 1 0]]
[[0 1 0 0 0 0 0 0 0 0 0] [0 1 0 0 0 0 0 0 0 0 0] [0 1 0 0 0 0 0 0 0 0 0] [0 1 0 0 0 0 0 0 0 0 0] [0 1 0 0 0 0 0 0 0 0 0] [0 1 0 0 0 0 0 0 0 0 0] [0 1 0 0 0 0 0 0 0 0 0] [0 0 0 0 0 0 0 0 0 1 0]]
[[0 0 1 0 0 0 0 0 0 0 0] [0 0 0 1 0 0 0 0 0 0 0] [0 0 0 0 1 0 0 0 0 0 0] [0 0 0 0 0 1 0 0 0 0 0] [0 0 0 0 0 0 1 0 0 0 0] [0 0 0 0 0 0 0 1 0 0 0] [0 0 0 0 0 0 0 0 861 0 0] [0 0 0 0 0 0 0 0 0 0 1]]
```
Calculate the witness given the R1CS 
input

input
[(x,3)]
witness
[1 3 9 27 81 243 729 2187 762656546057117603562592534677953835837922104544112694902376452493930609611 812283518468366721095433750743019157728318690555355044294444169641986292 15488755034149214877756480202726987801042521325895567363610570018460600916982]


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
