import "core:fmt.odin"
import "core:utf8.odin"


Kind :: enum {
	Illegal,
	EOF,
	Comment,

	_literal_start,
		Ident,
		Integer,
		Float,
		Char,
		String,
	_literal_end,

	_keyword_start,
		True,  // true
		False, // false
		Nil,   // nil
	_keyword_end,


	_operator_start,
		Question, // ?

		And,   // and
		Or,    // or

		Add,   // +
		Sub,   // -
		Mul,   // *
		Quo,   // /
		Rem,   // %

		Not,   // !

		Eq,    // ==
		NotEq, // !=
		Lt,    // <
		Gt,    // >
		LtEq,  // <=
		GtEq,  // >=

	_operator_end,

	_punc_start,
		Assign, // =

		Open_Paren,    // (
		Close_Paren,   // )
		Open_Bracket,  // [
		Close_Bracket, // ]
		Open_Brace,    // {
		Close_Brace,   // }

		Colon,     // :
		Semicolon, // ;
		Comma,     // ,
		Period,    // .
	_punc_end,
}


Pos :: struct {
	file:   string,
	line:   int,
	column: int,
}

Token :: struct {
	kind:      Kind,
	using pos: Pos,
	lit:       string,
}

Tokenizer :: struct {
	src: []u8,

	file:        string, // May not be used

	curr_rune:   rune,
	offset:      int,
	read_offset: int,
	line_offset: int,
	line_count:  int,

	insert_semi: bool,

	error_count: int,
}


keywords := map[string]Kind{
	"true"  = Kind.True,
	"false" = Kind.False,
	"nil"   = Kind.Nil,
	"and"   = Kind.And,
	"or"    = Kind.Or,
};

kind_to_string := [Kind.count]string{
	"illegal",
	"EOF",
	"comment",

	"",
	"identifier",
	"integer",
	"float",
	"character",
	"string",
	"",

	"",
	"true", "false", "nil",
	"",

	"",
	"?", "and", "or",
	"+", "-", "*", "/", "%",
	"!",
	"==", "!=", "<", ">", "<=", ">=",
	"",

	"",
	"=",
	"(", ")",
	"[", "]",
	"{", "}",
	":", ";", ",", ".",
	"",
};

precedence :: proc(op: Kind) -> int {
	using Kind;

	switch op {
	case Question:
		return 1;
	case Or:
		return 2;
	case And:
		return 3;
	case Eq, NotEq, Lt, Gt, LtEq, GtEq:
		return 4;
	case Add, Sub:
		return 5;
	case Mul, Quo, Rem:
		return 6;
	}
	return 0;
}


token_lookup :: proc(ident: string) -> Kind {
	if tok, is_keyword := keywords[ident]; is_keyword {
		return tok;
	}
	return Kind.Ident;
}

is_literal  :: proc(tok: Kind) -> bool do return Kind._literal_start  < tok && tok < Kind._literal_end;
is_operator :: proc(tok: Kind) -> bool do return Kind._operator_start < tok && tok < Kind._operator_end;
is_keyword  :: proc(tok: Kind) -> bool do return Kind._keyword_start  < tok && tok < Kind._keyword_end;


init :: proc(t: ^Tokenizer, src: []u8) {
	t.src = src;

	t.curr_rune   = ' ';
	t.offset      = 0;
	t.read_offset = 0;
	t.line_offset = 0;
	t.line_count  = 1;

	advance_to_next_rune(t);
	if t.curr_rune == utf8.RUNE_BOM {
		advance_to_next_rune(t);
	}
}

error :: proc(t: ^Tokenizer, msg: string, args: ...any) {
	fmt.printf_err("%s(%d:%d) Error: ", t.file, t.line_count, t.read_offset-t.line_offset+1);
	fmt.printf_err(msg, ...args);
	fmt.println_err();
	t.error_count += 1;
}

advance_to_next_rune :: proc(t: ^Tokenizer) {
	if t.read_offset < len(t.src) {
		t.offset = t.read_offset;
		if t.curr_rune == '\n' {
			t.line_offset = t.offset;
			t.line_count += 1;
		}
		r, w := rune(t.src[t.read_offset]), 1;
		switch {
		case r == 0:
			error(t, "Illegal character NUL");
		case r >= utf8.RUNE_SELF:
			r, w = utf8.decode_rune(t.src[t.read_offset..]);
			if r == utf8.RUNE_ERROR && w == 1 {
				error(t, "Illegal utf-8 encoding");
			} else if r == utf8.RUNE_BOM && t.offset > 0 {
				error(t, "Illegal byte order mark");
			}
		}

		t.read_offset += w;
		t.curr_rune = r;
	} else {
		t.offset = len(t.src);
		if t.curr_rune == '\n' {
			t.line_offset = t.offset;
			t.line_count += 1;
		}
		t.curr_rune = utf8.RUNE_EOF;
	}
}


get_pos :: proc(t: ^Tokenizer) -> Pos {
	return Pos {
		file   = t.file,
		line   = t.line_count,
		column = t.offset - t.line_offset + 1,
	};
}

is_letter :: proc(r: rune) -> bool {
	switch r {
	case 'a'...'z', 'A'...'Z', '_':
		return true;
	}
	return false;
}

is_digit :: proc(r: rune) -> bool {
	switch r {
	case '0'...'9':
		return true;
	}
	return false;
}

skip_whitespace :: proc(t: ^Tokenizer) {
	loop: for {
		switch t.curr_rune {
		case '\n':
			if t.insert_semi {
				break loop;
			}
			fallthrough;
		case ' ', '\t', '\r':
			advance_to_next_rune(t);
		}

		break loop;
	}
}

scan_identifier :: proc(t: ^Tokenizer) -> string {
	offset := t.offset;
	for is_letter(t.curr_rune) || is_digit(t.curr_rune) {
		advance_to_next_rune(t);
	}
	return string(t.src[offset .. t.offset]);
}

digit_value :: proc(r: rune) -> int {
	switch r {
	case '0'...'9': return int(r - '0');
	case 'a'...'f': return int(r - 'a' + 10);
	case 'A'...'F': return int(r - 'A' + 10);
	}
	return 16;
}

scan_number :: proc(t: ^Tokenizer, seen_decimal_point: bool) -> (Kind, string) {
	scan_manitissa :: proc(t: ^Tokenizer, base: int) {
		for digit_value(t.curr_rune) < base {
			advance_to_next_rune(t);
		}
	}
	scan_exponent :: proc(t: ^Tokenizer, tok: Kind, offset: int) -> (Kind, string) {
		if t.curr_rune == 'e' || t.curr_rune == 'E' {
			tok = Kind.Float;
			advance_to_next_rune(t);
			if t.curr_rune == '-' || t.curr_rune == '+' {
				advance_to_next_rune(t);
			}
			if digit_value(t.curr_rune) < 10 {
				scan_manitissa(t, 10);
			} else {
				error(t, "Illegal floating point exponent");
			}
		}
		return tok, string(t.src[offset .. t.offset]);
	}
	scan_fraction :: proc(t: ^Tokenizer, tok: Kind, offset: int) -> (Kind, string) {
		if t.curr_rune == '.' {
			tok = Kind.Float;
			advance_to_next_rune(t);
			scan_manitissa(t, 10);
		}

		return scan_exponent(t, tok, offset);
	}

	offset := t.offset;
	tok := Kind.Integer;

	if seen_decimal_point {
		offset -= 1;
		tok = Kind.Float;
		scan_manitissa(t, 10);
		return scan_exponent(t, tok, offset);
	}

	if t.curr_rune == '0' {
		offset := t.offset;
		advance_to_next_rune(t);
		switch t.curr_rune {
		case 'b', 'B':
			advance_to_next_rune(t);
			scan_manitissa(t, 2);
			if t.offset - offset <= 2 {
				error(t, "Illegal binary number");
			}
		case 'o', 'O':
			advance_to_next_rune(t);
			scan_manitissa(t, 8);
			if t.offset - offset <= 2 {
				error(t, "Illegal octal number");
			}
		case 'x', 'X':
			advance_to_next_rune(t);
			scan_manitissa(t, 16);
			if t.offset - offset <= 2 {
				error(t, "Illegal hexadecimal number");
			}
		case:
			scan_manitissa(t, 10);
			switch t.curr_rune {
			case '.', 'e', 'E':
				return scan_fraction(t, tok, offset);
			}
		}

		return tok, string(t.src[offset .. t.offset]);
	}

	scan_manitissa(t, 10);

	return scan_fraction(t, tok, offset);
}

scan :: proc(t: ^Tokenizer) -> Token {
	skip_whitespace(t);

	offset := t.offset;

	tok: Kind;
	pos := get_pos(t);
	lit: string;

	insert_semi := false;


	switch r := t.curr_rune; {
	case is_letter(r):
		lit = scan_identifier(t);
		tok = Kind.Ident;
		if len(lit) > 1 {
			tok = token_lookup(lit);
		}
		if tok == Kind.Ident {
			insert_semi = true;
		}

	case '0' <= r && r <= '9':
		insert_semi = true;
		tok, lit = scan_number(t, false);

	case:
		advance_to_next_rune(t);
		switch r {
		case -1:
			if t.insert_semi {
				t.insert_semi = false;
				return Token{Kind.Semicolon, pos, "\n"};
			}
			return Token{Kind.EOF, pos, "\n"};

		case '\n':
			t.insert_semi = false;
			return Token{Kind.Semicolon, pos, "\n"};

		case '"':
			quote := r;
			tok = Kind.String;
			for {
				r := t.curr_rune;
				if r == '\n' || r < 0 {
					error(t, "String literal not terminated");
					break;
				}
				advance_to_next_rune(t);
				if r == quote {
					break;
				}
				// TODO(bill); Handle properly
				if r == '\\' && t.curr_rune == quote {
					advance_to_next_rune(t);
				}
			}

			lit = string(t.src[offset+1..t.offset-1]);


		case '#':
			for t.curr_rune != '\n' && t.curr_rune >= 0 {
				advance_to_next_rune(t);
			}
			advance_to_next_rune(t);
			tok = Kind.Semicolon;
			lit = ";";

		case '?': tok = Kind.Question;
		case ':': tok = Kind.Colon;

		case ',': tok = Kind.Comma;
		case ';': tok = Kind.Semicolon;
		case '(': tok = Kind.Open_Paren;
		case ')': tok = Kind.Close_Paren; insert_semi = true;

		case '[': tok = Kind.Open_Bracket;
		case ']': tok = Kind.Close_Bracket; insert_semi = true;

		case '{': tok = Kind.Open_Brace;
		case '}': tok = Kind.Close_Brace; insert_semi = true;

		case '+': tok = Kind.Add;
		case '-': tok = Kind.Sub;
		case '*': tok = Kind.Mul;
		case '/': tok = Kind.Quo;
		case '%': tok = Kind.Rem;

		case '!':
			tok = Kind.Not;
			if t.curr_rune == '=' {
				advance_to_next_rune(t);
				tok = Kind.NotEq;
			}

		case '=':
			tok = Kind.Assign;
			if t.curr_rune == '=' {
				advance_to_next_rune(t);
				tok = Kind.Eq;
			}

		case '<':
			tok = Kind.Lt;
			if t.curr_rune == '=' {
				advance_to_next_rune(t);
				tok = Kind.LtEq;
			}

		case '>':
			tok = Kind.Gt;
			if t.curr_rune == '=' {
				advance_to_next_rune(t);
				tok = Kind.GtEq;
			}

		case '.':
			if '0' <= t.curr_rune && t.curr_rune <= '9' {
				insert_semi = true;
				tok, lit = scan_number(t, true);
			} else {
				tok = Kind.Period;
			}

		case:
			if r != utf8.RUNE_BOM {
				error(t, "Illegal character %r", r);
			}
			insert_semi = t.insert_semi;
			tok = Kind.Illegal;
		}
	}

	t.insert_semi = insert_semi;

	if lit == "" {
		lit = string(t.src[offset .. t.offset]);
	}

	return Token{tok, pos, lit};
}
