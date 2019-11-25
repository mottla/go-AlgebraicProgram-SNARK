package circuitcompiler

import (
	"fmt"
	"testing"

	"github.com/go-lexer"
)

func Test_LexerError2(t *testing.T) {
	code := `def main(a):
		for(a = 3; a<3; a+=1){
			var d =  (c * (1+b) * k)
		}		
		return  d `

	fmt.Println(code)
	l := lexer.New(code, lexer.ProbablyWhitespaceState)
	l.Start()
	tok, done := l.NextToken()
	for !done {
		fmt.Printf("%v , %q \n", tok.Type, tok.Value)
		tok, done = l.NextToken()
	}

	fmt.Println("done")

}
