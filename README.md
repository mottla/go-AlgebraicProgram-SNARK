# go-AlgebraicProgram-SNARK
**UNDER CONSTRUCTION**

zkSNARK toolchain 
Attempt to extend the language from quadratic arithmetic programs to
an algebraic circuit based zkSNARK.
Eg. we use circuits with (+ , - , * , / , g^ ) where g is a generator point of the EC Group G1. 
Theoretic description ![PDF](algebraicProgramSNARK.pdf).
Code examples can be found  ![here](testPrograms/codes.go).
If the extension is disabled, we have a classic zkSNARK creation toolchain.

Note that this scheme is not secure since blind evaluation is restricted to the gates indices rather then to an arbitrary 
point in the underlying finite field, however
somebody might come up with a smart idea how to overcome this issue.
It would be nice, since a shielded transaction (Zcash) would take milliseconds instead of seconds!

**Circuit Language**
This toolchain comes along with a compiler fully written in go.
My goal was, to create a compiler for a language that is as close to golang as possible.
The language supports functional paradigm. Functions and field elements are the only first class citizen e.g.
functions can be passed as arguments (see example).
Due to the nature of zkSNARKs (only programs of static size) some things such as dynamic looping, jumps, dynamic array access etc. cannot be supported.

This language then gets compiled into a R1CS form, with focus on gate reduction.
We reuse gates whenever possible, exploit commutative properties of the gates, extract constant factors as long as possible etc.
# Language

## main
every program starts with the function 'main' 
```
func main(){
#this is a comment
}
```
main can be fed with an arbitrary amount of single arguments and n-dimensional static size arrays of single values
```
func main(a,b[2],c[3][42],d){
}
```
## Declare public inputs
in order to declare, which of the main inputs will be part of the public statement of the SNARK, write
```
func main(a,b[2],c[3][42],d){
    public{
        a, b[1],c[0][0]
    }
}
```
## variables
expressions need to be assigned, passed as arguments or returned. They cannot be unasigned (as in Golang)
```
func main(x){
    #constants
    var purposeOfLive = 42*17
    #variable
    var xSquared = x*x
    return purposeOfLive*xSquared
}
```
also valid
```
func main(x){   
    var purposeOfLive = 42*17   
    var xSquared = x*x
    return doSomething(purposeOfLive*xSquared)
}
func doSomething(a){
    ....
}
```

invalid however
```
func main(x){
    #constants
    var purposeOfLive = 42*17
    #variable
    var xSquared = x*x
    purposeOfLive*xSquared #missing assignment!!
    return 
}
```
## Declare Functions
functions can be declared outside the scope of main
```
func main(x){
    ...   
}
func foo(input){
}
```
functions can also be declared inside the scope of a function via
```
func asdf(...){
    func foo(...){
      ..
    }   
    #call foo inside asdf with foo(args) 
}
```
equivalently
```
func asdf(...){
    var foo = func(...){
      ..
    }    
}
```
## Functions as arguments
functions can be passed as arguments
```
func main(x){
    var multiplyWith5 = func(a){return a*5}
    executeFkt(multiplyWith5,x) # we execute multiplyWith5 now in the executeFkt
}
func executeFkt(fkt,input){
    #fkt must be a function, which takes at least one argument
    return fkt(input)
}
```
## Function preloading
functions can be partially executed
```
func main(x){
    var multiply = func(a,b){return a*b}
    var multiplyBy5 = multiply(5)
    multiplyBy5(x) #is now the same as multiply(5,x) 
}
```
functions return functions, as long as they are not completely filled with all required inputs
(constants are also functions, but the empty () can be omitted. everything is a function. even the universe)
## Loop
for those who like loops write
```
for ( staticBooleanComparisonExpression ; incrementStatement){
}
```
example:
```
func main(x){
    var i = 0       #declare the running variable outside
    for ( i <= 43 ; i = i+1){  #we dont support ++, +=, -=, etc.. currently
    }
}
```
## if-else if-else
in order to create braching conditions, write:
```
if expression1{ 
    ...
}else if expression2{
    ...
}else if expression3{
    ...
}else{
    ...
}
```
note that we currently only support static decidable branching conditions

## arrays
declare an array with
```
var myArray[] = {a,b,3}
```
access myArray with
```
myArray[x]
```
where x can be 0,1,2 in this example.

# SNARK stuff
## euquality assertion gate
in order to create an equality assertion constraint write
```
equal(expression1,expression2)
```
example: in order to ensure that the user knew x,y s.t. x= 5y in zero Knowledge write
```
func main(x,y){
   equal(x,5y)
}
```
## split 
to split a value into its bit representatives write
```
SPLIT(x)
```
now the i'th bit of x can be accessed with x[i], where x[0] is the least significant bit


## Example of classic SNARK


```
#comment
#every programm need a main with arbitrarily many field elements as arguments
func main(x){
   
    #functions can be declared within functions
    var a = func(i){
        if i == 0 {
            return
        }        
        return x*a(i-1)			
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


# Example of extended algebraic program SNARK
(see ![PDF](algebraicProgramSNARK.pdf) for the mathematical background.)
**note that this extension is not sound and should not be used in production**
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
The EAP then has the form :
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
