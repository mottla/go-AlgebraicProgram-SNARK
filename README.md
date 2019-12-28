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

**Example of classic SNARK** (without the extention explained in the ![PDF](algebraicProgramSNARK.pdf))

```
def main(x,z,w) {
    var k = x*x*(7-4)	
    var arra[]={k,1,2,3}
    k = arra[0]*k
    var l = mul( (k*7)+(3*z) )
    equal(l,w)
    #this is a comment
    return l*(k*arra[2*2/2])
}

def mul(a){
    return a*a	
}


R1SC form of the code above. 
Note that the big number at the end is because we do arithmetic on a finite field and we extract factors as long as possible to reduce gates.
so inverses and negative numbers are likely huge.
[[0 1 0 0 0 0 0 0] [0 0 0 0 1 0 0 0] [0 0 3 0 0 7 0 0] [0 0 0 0 0 0 1 0] [0 0 0 0 0 1 0 0]]
[[0 1 0 0 0 0 0 0] [0 0 0 0 1 0 0 0] [0 0 3 0 0 7 0 0] [1 0 0 0 0 0 0 0] [0 0 0 0 0 0 1 0]]
[[0 0 0 0 1 0 0 0] [0 0 0 0 0 1 0 0] [0 0 0 0 0 0 1 0] [0 0 0 1 0 0 0 0] [0 0 0 0 0 0 0 10944121435919637611123202872628637544274182200208017171849102093287904247809]]
input
[x=3 z=2 w=328329]
witness
[1 3 2 328329 9 81 328329 53189298]
--- PASS: TestCorrectness (0.00s)
PASS

```
