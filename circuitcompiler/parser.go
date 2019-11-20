package circuitcompiler

import (
	"errors"
	"fmt"
)

// Constraint is the data structure of a flat code operation
type Constraint struct {
	// v1 op v2 = out
	Output Token

	Inputs []*Constraint // in func declaration case

}
type ParseState func(parser *Parser) ParseState

func (c Constraint) String() string {
	//fmt.Sprintf("|%v , %v|", c.Output, c.Inputs)
	return fmt.Sprintf("|%v|", c.Output)
}

func (c Constraint) PrintConstaintTree(depth int) {
	fmt.Printf("%v: %v \n", depth, c)
	depth++
	for _, v := range c.Inputs {
		v.PrintConstaintTree(depth)
	}

}
func (c Constraint) PrintReverseConstaintTree(depth int) {

	depth++
	for _, v := range c.Inputs {
		v.PrintReverseConstaintTree(depth)
	}
	fmt.Printf("%v: %v \n", depth, c)
}

type Parser struct {
	lexer          *L
	ErrorHandler   func(e string)
	Err            error
	tokenChannel   chan Token
	done           chan struct{}
	log            bool
	constraintChan chan Constraint

	//constraintBuilder chan<- Token
}

func (l *Parser) Error(e string, a ...interface{}) {
	if l.ErrorHandler != nil {
		l.Err = errors.New(fmt.Sprintf(e, a...))
		l.ErrorHandler(e)
	} else {
		//since parser and lexer run concurrently, we use the lexers error handler, to get the line-number where the program failed
		l.lexer.Error(fmt.Sprintf(e, a...))
		//panic(fmt.Sprintf("%v ", e, ))
	}
}
func (p *Parser) NextNonBreakToken() *Token {
	tok, done := p.lexer.NextToken()
	if done {
		close(p.done)
		return &Token{Type: EOF}
	}
	for tok.Type == CommentToken {
		tok = p.NextToken()
	}
	for tok.Value == "\n" {
		tok = p.NextToken()
	}
	return tok
}

func (p *Parser) NextToken() *Token {
	tok, done := p.lexer.NextToken()
	if done {
		close(p.done)
		return &Token{Type: EOF}
	}
	for tok.Type == CommentToken {
		tok = p.NextToken()
	}
	return tok
}

func NewParser(code string, log bool) (p *Parser) {
	lexer := New(code, ProbablyWhitespaceState)
	lexer.Start()
	return &Parser{constraintChan: make(chan Constraint), tokenChannel: make(chan Token), done: make(chan struct{}), lexer: lexer, log: log}
}

func (parser *Parser) Parse(programm *Program) {

	var circuit *Circuit

	go parser.libraryMode()
out:
	for {
		select {
		case constraint := <-parser.constraintChan:
			fmt.Println(constraint)

			if constraint.Output.Type == FUNCTION_DEFINE {
				if _, ex := programm.functions[constraint.Output.Value]; ex {
					panic(fmt.Sprintf("function %s already declared", constraint.Output.Value))
				}
				circuit = RegisterFunctionFromConstraint(&constraint)
				programm.functions[constraint.Output.Value] = circuit
				continue
			}
			circuit.SemanticCheck_RootMapUpdate(&constraint)

			constraint.PrintReverseConstaintTree(0)
		case <-parser.done:
			break out
		}
	}

}

func (p *Parser) libraryMode() {
	if p.log {
		fmt.Println("library mode")
	}

	tok := p.NextNonBreakToken()

	if tok.Type == FUNCTION_DEFINE {
		p.functionMode()
		p.libraryMode()
		return
	}
	if tok.Value == "" {
		//close(p.done)
		return
	}
	p.Error("Function expected, got %v : %v", tok.Value, tok.Type)

}

func (p *Parser) functionMode() {
	if p.log {
		fmt.Println("function mode")
	}
	tok := p.NextToken()

	//we expect an identifier
	if tok.Type != IdentToken {
		p.Error("Function Identifier expected, got %v : %v", tok.Value, tok.Type)
	}

	FuncConstraint := &Constraint{
		Output: Token{Type: FUNCTION_DEFINE, Value: tok.Value},
	}

	tok = p.NextToken()

	if tok.Value != "(" {
		p.Error("function needs brackets, got %v : %v", tok.Value, tok.Type)
	}

	for {
		tok = p.NextToken()
		if tok.Type == IdentToken {
			FuncConstraint.Inputs = append(FuncConstraint.Inputs, &Constraint{Output: Token{Type: ARGUMENT, Value: tok.Value}})

			continue
		}
		if tok.Value == "," {
			continue
		}
		if tok.Value == ")" {
			break
		}
		p.Error("Invalid function header, got %v : %v", tok.Value, tok.Type)

	}
	tok = p.NextToken()
	if tok.Value != "{" {
		p.Error("invalid function declaration, got %v : %v", tok.Value, tok.Type)
	}
	p.constraintChan <- *FuncConstraint
	toks := p.stackTillSwingBracketsClose()
	p.statementMode(toks)
	return

}

func (p *Parser) statementMode(tokens []Token) {
	if p.log {
		fmt.Println("statement mode")
	}
	tokens = removeLeadingAndTrailingBreaks(tokens)
	if len(tokens) == 0 {
		return
	}
	var success bool
	switch tokens[0].Type {
	case IF: //if a<b { }   if (a<b) {
		ifStatement, rest := SplitAtFirst(tokens, "{")
		if len(rest) == 0 || rest[0].Value != "{" {
			p.Error("if statement requires { }")
		}
		insideIf, outsideIf, success := SplitAtClosingSwingBrackets(rest[1:])
		if !success {
			p.Error("closing } brackets missing around IF body")
		}

		ifStatement = removeTrailingBreaks(ifStatement)
		IfConst := Constraint{
			Output: Token{
				Type: IF,
			},
		}
		p.expressionMode(ifStatement[1:], &IfConst)
		p.statementMode(insideIf)
		p.statementMode(outsideIf)
		return
	case FOR:
		// for ( a = 4; a<5 ; a+=1)

		if tokens[1].Value != "(" {
			p.Error("brackets '(' missing, got %v", tokens[1])
		}
		// a = 4;
		l, r := SplitAtFirst(tokens[2:], ";")
		if r[0].Value != ";" {
			p.Error("';' expected, got %v", r[0])
		}
		r = r[1:]
		if b, err := isAssignment(l); !b {
			p.Error(err)
		}
		varConst := Constraint{
			Output: Token{
				Type:  VAR,
				Value: l[0].Value,
			},
		}
		ForConst := Constraint{Output: Token{Type: FOR}, Inputs: []*Constraint{&varConst}}

		p.expressionMode(l[2:], &ForConst)

		// a <5;
		l, r = SplitAtFirst(r, ";")
		if r[0].Value != ";" {
			p.Error("';' expected, got %v", r[0])
		}
		r = r[1:]
		p.expressionMode(l, &ForConst)
		//a+=1)
		l, r, success = SplitAtClosingBrackets(r)
		if !success {
			p.Error("closing brackets missing")
		}
		p.expressionMode(l, &ForConst)
		p.constraintChan <- ForConst
		r = removeLeadingBreaks(r)

		if r[0].Value != "{" {
			p.Error("brackets '{' missing, got %v", r[0])
		}
		l, r, success = SplitAtClosingSwingBrackets(r[1:])
		if !success {
			p.Error("closing brackets missing")
		}
		p.statementMode(l)
		p.statementMode(r)
	case VAR:

		l, r := SplitAtFirst(tokens, "\n")
		if r[0].Value != "\n" {
			p.Error("linebreak expected, got %v", r[0])
		}
		r = r[1:]
		//var hannes = 42
		if b, err := isAssignment(l[1:]); !b {
			p.Error(err)
		}
		varConst := Constraint{
			Output: Token{
				Type:  VAR,
				Value: l[1].Value,
			},
		}
		p.expressionMode(l[3:], &varConst)
		p.constraintChan <- varConst
		p.statementMode(r)
	case RETURN:
		//return (1+a)
		l, r := SplitAtFirst(tokens, "\n")
		returnCOnstraint := Constraint{
			Output: Token{
				Type: RETURN,
			},
		}
		p.expressionMode(l[1:], &returnCOnstraint)
		p.constraintChan <- returnCOnstraint
		if len(removeLeadingAndTrailingBreaks(r)) != 0 {
			panic("not supposed")
		}
		return

	default:
		p.Error("return missing maybe")
	}
}

// epx := (exp) | exp Operator exp | Identifier(arg) | IN | Number
//arg := exp | arg,exp
func (p *Parser) expressionMode(stack []Token, constraint *Constraint) {
	if len(stack) == 0 {
		return
	}
	if stack[0].Value == "(" {
		// asdf)jkl -> { asdf, )jkl }
		withinBrackets, outsideBrackets, success := SplitAtClosingBrackets(stack[1:])
		if !success {
			p.Error("closing brackets missing")
		}
		newTok := Token{
			Type:  IdentToken,
			Value: combineString(withinBrackets) + ")",
		}
		c1 := &Constraint{Output: newTok}

		constraint.Inputs = append(constraint.Inputs, c1)
		//p.tokenChannel <- newTok
		p.expressionMode(withinBrackets, c1)

		if len(outsideBrackets) > 1 {
			p.expressionMode(append([]Token{newTok}, outsideBrackets...), constraint)
		}

		return
	}

	//can only be a In or a Number
	if len(stack) == 1 {
		if stack[0].Type == NumberToken || stack[0].Type == IdentToken {
			constraint.Inputs = append(constraint.Inputs, &Constraint{Output: stack[0]})
			return
		}
		p.Error("Variable or number expected, got %v ", stack[0])
	}

	//can be exp Op exp | Indentifier(arg)
	if len(stack) >= 3 {
		if stack[0].Type != NumberToken && stack[0].Type != IdentToken {
			p.Error("Variable or number expected, got %v ", stack[0])
		}

		if stack[1].Type == BinaryComperatorToken ||
			stack[1].Type == ArithmeticOperatorToken ||
			stack[1].Type == BooleanOperatorToken ||
			stack[1].Type == BitOperatorToken ||
			stack[1].Type == AssignmentOperatorToken {

			constraint.Inputs = append(constraint.Inputs, &Constraint{Output: stack[0]}, &Constraint{Output: stack[1]})
			if len(stack) == 3 {
				p.expressionMode(stack[2:], constraint)
				return
			}

			out := combineString(stack[2:])

			newTok := Token{
				Type:  IdentToken,
				Value: out,
			}
			c1 := &Constraint{Output: newTok}
			constraint.Inputs = append(constraint.Inputs, c1)

			p.expressionMode(stack[2:], c1)
			return
		}

		if stack[0].Type != IdentToken {
			p.Error("function name expected, got %v ", stack[0])
		}

		if stack[1].Value == "(" {
			newTok := Token{
				Type:  FUNCTION_CALL,
				Value: stack[0].Value,
			}
			c1 := &Constraint{Output: newTok}
			constraint.Inputs = append(constraint.Inputs, c1)
			functionInput, rem, success := SplitAtClosingBrackets(stack[2:])
			if !success {
				p.Error("closing brackets missing")
			}
			for _, v := range SplitAt(functionInput, ",") {
				//TODO check soon
				if len(v) == 0 {
					p.Error("argument missing at function %v", stack[0].Value)
				}
				p.expressionMode(v, c1)
			}
			if len(rem) == 0 {
				return
			}
			if len(rem) == 1 {
				p.expressionMode(rem, constraint)
				return
			}
			if len(rem) > 1 {
				out := combineString(stack[:len(functionInput)]) + ")"
				newTok := Token{
					Type:  IdentToken,
					Value: out,
				}
				//c1 := &Constraint{Output: newTok}
				//constraint.Inputs = append(constraint.Inputs, c1)
				p.expressionMode(append([]Token{newTok}, rem...), constraint)
				return
			}
		}
		return
	}
	p.Error("invalid expression , got %v ", stack)
	return
}

func removeTrailingBreaks(in []Token) (out []Token) {
	if len(in) == 0 {
		return
	}
	if in[len(in)-1].Value == "\n" {
		return removeLeadingBreaks(in[:len(in)-1])
	}
	return in
}
func removeLeadingAndTrailingBreaks(in []Token) (out []Token) {
	return removeLeadingBreaks(removeTrailingBreaks(in))
}

func removeLeadingBreaks(in []Token) (out []Token) {
	if len(in) == 0 {
		return
	}
	if in[0].Value == "\n" {
		return removeLeadingBreaks(in[1:])
	}
	return in

}

func combineString(in []Token) string {
	out := ""
	for _, s := range in {
		out += s.Value
	}
	return out
}

func isAssignment(stx []Token) (yn bool, err string) {
	if len(stx) < 3 {
		return false, "assignment needs min 3 tokens: a = b"
	}
	if stx[0].Type != IdentToken {
		return false, "identifier expected"
	}
	if stx[1].Type != AssignmentOperatorToken {
		return false, "assignment  expected"
	}
	return true, ""
}

//the closing } is not in the returned tokens array
func (p *Parser) stackTillSwingBracketsClose() (tokens []Token) {
	var stack []Token
	ctr := 1
	for tok := p.NextToken(); tok.Type != EOF; tok = p.NextToken() {
		if tok.Value == "{" {
			ctr++
		}
		if tok.Value == "}" {
			ctr--
			if ctr == 0 {
				return stack
			}

		}
		stack = append(stack, *tok)
	}
	p.Error("closing } missing")
	return
}

//func (p *Parser) stackTillEOReturn() []Token {
//	var stack []Token
//	for tok := p.NextToken(); tok.Type != EOF; tok = p.NextToken() {
//		stack = append(stack, *tok)
//		if tok.Type == RETURN {
//			return append(stack, p.stackTillBreak()...)
//		}
//	}
//	p.Error("return missing")
//	return stack
//}

func (p *Parser) stackTillBreak() []Token {
	var stack []Token
	for tok := p.NextToken(); tok.Value != "\n" || tok.Type == EOF; tok = p.NextToken() {
		stack = append(stack, *tok)
	}
	return stack
}
func (p *Parser) stackTillSemiCol() []Token {
	var stack []Token
	for tok := p.NextToken(); tok.Value != "\n" || tok.Type != EOF; tok = p.NextToken() {
		if tok.Value == ";" {
			return stack
		}
		stack = append(stack, *tok)
	}
	p.Error("no ';' found")
	return nil
}

//SplitAt takes takes a string S and a token array and splits st: abScdasdSf -> ( ab,cdas, f  )
//if S does not occur it returns ( in , []Tokens{} )
func SplitAt(in []Token, splitAt string) (out [][]Token) {
	for l, r := SplitAtFirst(in, splitAt); ; l, r = SplitAtFirst(r, splitAt) {
		if len(l) > 0 {
			out = append(out, l)
			continue
		}
		if len(r) > 1 && r[0].Value == splitAt {
			r = r[1:]
			continue
		}
		return
	}
}

//SplitAtFirst takes takes a string S and a token array and splits st: abScd -> ( ab , Scd )
//if S does not occur it returns ( in , []Tokens{} )
func SplitAtFirst(in []Token, splitAt string) (cutLeft, cutRight []Token) {
	for i := 0; i < len(in); i++ {
		if in[i].Value == splitAt {
			return in[:i], in[i:]
		}
	}
	return in, cutRight
}

//SplitAtClosingBrackets takes token array asserting that the opening brackets
//are not contained! Returns the slices without the closing bracket in an of them!
//note that this behaviour differs from SplitAtFirst
//example "asdf)jkl" -> "asdf" ,"jkl" ,true
//"(asdf)jkl" -> nil,nil,false
//"(asdf))jkl" -> "(asdf)","jkl",true
func SplitAtClosingBrackets(in []Token) (cutLeft, cutRight []Token, success bool) {
	ctr := 1
	for i := 0; i < len(in); i++ {
		if in[i].Value == "(" {
			ctr++
		}
		if in[i].Value == ")" {
			ctr--
			if ctr == 0 {
				if i == len(in)-1 {
					return in[:i], cutRight, true
				}
				return in[:i], in[i+1:], true
			}
		}
	}
	return nil, nil, false
}
func SplitAtClosingSwingBrackets(in []Token) (cutLeft, cutRight []Token, success bool) {
	ctr := 1
	for i := 0; i < len(in); i++ {
		if in[i].Value == "{" {
			ctr++
		}
		if in[i].Value == "}" {
			ctr--
			if ctr == 0 {
				if i == len(in)-1 {
					return in[:i], cutRight, true
				}
				return in[:i], in[i+1:], true
			}
		}
	}
	return nil, nil, false
}

func (p *Parser) CutAtSemiCol(in []Token) (cut []Token) {
	if len(in) == 0 {
		return
	}
	if in[len(in)-1].Value == ";" {
		return in[:len(in)-1]
	}

	return p.CutAtSemiCol(in[:len(in)-1])
}

//func (p *Parser) stackTillBracketsClose() []Token {
//	var stack []Token
//	ctr := 1
//	for tok := p.NextToken(); tok.Value != "\n" || tok.Type != EOF; tok = p.NextToken() {
//
//		if tok.Value == "(" {
//			ctr++
//		}
//		if tok.Value == ")" {
//			ctr--
//			if ctr == 0 {
//				return stack
//			}
//		}
//		stack = append(stack, *tok)
//	}
//	p.Error("brackets missmatch")
//	return nil
//}

//
//import (
//	"errors"
//	"io"
//	"strings"
//)
//
//// Parser data structure holds the Scanner and the Parsing functions
//type Parser struct {
//	s   *Scanner
//	buf struct {
//		tok Token  // last read token
//		lit string // last read literal
//		n   int    // buffer size (max=1)
//	}
//}
//
//// NewParser creates a new parser from a io.Reader
//func NewParser(r io.Reader) *Parser {
//	return &Parser{s: NewScanner(r)}
//}
//
//func (p *Parser) scan() (tok Token, lit string) {
//	// if there is a token in the buffer return it
//	if p.buf.n != 0 {
//		p.buf.n = 0
//		return p.buf.tok, p.buf.lit
//	}
//	tok, lit = p.s.scan()
//
//	p.buf.tok, p.buf.lit = tok, lit
//
//	return
//}
//
//func (p *Parser) unscan() {
//	p.buf.n = 1
//}
//
//func (p *Parser) scanIgnoreWhitespace() (tok Token, lit string) {
//	tok, lit = p.scan()
//	if tok == WS {
//		tok, lit = p.scan()
//	}
//	return
//}
//
//// parseLine parses the current line
//func (p *Parser) parseLine() (*Constraint, error) {
//	/*
//		in this version,
//		line will be for example s3 = s1 * s4
//		this is:
//		val eq val op val
//	*/
//	c := &Constraint{}
//	tok, lit := p.scanIgnoreWhitespace()
//	switch lit {
//	case "def":
//		c.Op = FUNC
//		// format: `func name(in):`
//		//todo this is all a bit hacky and unsafe
//		line, err := p.s.r.ReadString(':')
//		line = strings.Replace(line, " ", "", -1)
//		line = strings.Replace(line, ":", "", -1)
//		//set function name
//		//c.Literal = strings.Split(line, "(")[0]
//		c.Out = line
//
//		if err != nil {
//			return c, err
//		}
//		// read string inside ( )
//
//		return c, nil
//	case "var":
//		//var a = 234
//		//c.Literal += lit
//		_, lit = p.scanIgnoreWhitespace()
//		c.Out = lit
//		//c.Literal += lit
//		_, lit = p.scanIgnoreWhitespace() // skip =
//		//c.Literal += lit
//		// v1
//		_, lit = p.scanIgnoreWhitespace()
//		c.V1 = lit
//		//c.Literal += lit
//		break
//	case "#":
//		return nil, errors.New("comment parseline")
//	default:
//		c.Out = lit
//		//c.Literal += lit
//		_, lit = p.scanIgnoreWhitespace() // skip =
//		//c.Literal += lit
//
//		// v1
//		tok, lit = p.scanIgnoreWhitespace()
//		c.V1 = lit
//		//c.Literal += lit
//
//		// operator
//		tok, lit = p.scanIgnoreWhitespace()
//
//		c.Op = tok
//		//c.Literal += lit
//		// v2
//		_, lit = p.scanIgnoreWhitespace()
//		c.V2 = lit
//		//c.Literal += lit
//	}
//
//	if tok == EOF {
//		return nil, errors.New("eof in parseline")
//	}
//	return c, nil
//}
//
//// Parse parses the lines and returns the compiled Circuit
//func (p *Parser) Parse(programm *Program) (err error) {
//
//	var circuit *Circuit
//
//	for {
//		constraint, err := p.parseLine()
//		if err != nil {
//			break
//		}
//		if constraint.Op == FUNC {
//			circuit = programm.RegisterFunctionFromConstraint(constraint)
//		} else {
//			circuit.prepareAndAddConstraintToGateMap(constraint)
//		}
//	}
//
//	return nil
//}
