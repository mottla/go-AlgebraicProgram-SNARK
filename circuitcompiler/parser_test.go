package circuitcompiler

import (
	"fmt"
	"testing"
)

func Test_Parser(t *testing.T) {

	code := `def main(a){	
			var d =  asdf(a(x ),b,   c,d,  32 )			* 3
			return  d
		}

		def foo(o,k){
			for(a = 3; a<2; a+=1){
				var d =  (c * (1+b) * k)		
				return  d
				}
			if a<b{
					return foo()
				}
			return d * i			
		}  
	`
	fmt.Println(code)

	parser := NewParser(code, false)
	parser.Parse(false)
}

//only to see the difference between the split funcitons
func TestParser_SplitAt(t *testing.T) {
	toks := []Token{
		{
			Value: "a",
		},
		{
			Value: "b",
		},
		{
			Value: "c",
		},
		{
			Value: "a",
		},
		{
			Value: "e",
		},
		{
			Value: ")",
		},
		{
			Value: "a",
		},
	}

	fmt.Println(SplitTokensAtFirstString(toks, ")"))

	fmt.Println(SplitAt(toks, ")"))

	fmt.Println(SplitAtClosingBrackets(toks))
}
