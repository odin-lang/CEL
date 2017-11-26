import "core:fmt.odin"
import "core:strconv.odin"
import "core:os.odin"
import "core:raw.odin"
import "token.odin"


Array :: []Value;
Dict  :: map[string]Value;
Nil_Value :: struct{};

Value :: union {
	Nil_Value,
	bool, i64, f64, string,
	Array, Dict,
}

Parser :: struct {
	tokens:           [dynamic]token.Token,
	prev_token:       token.Token,
	curr_token:       token.Token,
	curr_token_index: int,

	allocated_strings: [dynamic]string,

	error_count: int,

	root: Dict,
	dict_stack: [dynamic]^Dict, // NOTE: Pointers may be stored on the stack
}


print_value :: proc(value: Value, pretty := true, indent := 0) {
	print_indent :: proc(indent: int) {
		for i in 0..indent do fmt.print("\t");
	}

	switch v in value {
	case bool: fmt.print(v);
	case i64: fmt.print(v);
	case f64: fmt.print(v);
	case string: fmt.print(v);
	case Array:
		fmt.print("[");
		if pretty do fmt.println();
		for e, i in v {
			if pretty {
				print_indent(indent+1);
				print_value(e, pretty, indent+1);
				fmt.println(",");
			} else {
				if i > 0 do fmt.print(", ");
				print_value(e);
			}
		}
		if pretty do print_indent(indent);
		fmt.print("]");
	case Dict:
		fmt.print("{");
		if pretty do fmt.println();

		i := 0;
		for name, value in v {
			if pretty {
				print_indent(indent+1);
				fmt.printf("%s = ", name);
				print_value(value, pretty, indent+1);
				fmt.println(",");
			} else {
				if i > 0 do fmt.print(", ");
				fmt.printf("%s = ", name);
				print_value(value, pretty, indent+1);
				i += 1;
			}
		}

		if pretty do print_indent(indent);
		fmt.print("}");
	case:
		fmt.print("nil");
	case Nil_Value:
		fmt.print("nil");
	}
}
print :: proc(p: ^Parser, pretty := false) {
	for name, val in p.root {
		fmt.printf("%s = ", name);
		print_value(val, pretty);
		fmt.println(";");
	}
}


parser_init :: proc(p: ^Parser, t: ^token.Tokenizer) -> bool {
	for {
		tok := token.scan(t);
		if tok.kind == token.Kind.Illegal {
			return false;
		}
		append(&p.tokens, tok);
		if tok.kind == token.Kind.EOF {
			break;
		}
	}

	if t.error_count > 0 {
		return false;
	}

	if len(p.tokens) == 0 {
		tok := token.Token{kind = token.Kind.EOF};
		tok.line, tok.column = 1, 1;
		append(&p.tokens, tok);
		return true;
	}

	p.curr_token_index = 0;
	p.prev_token = p.tokens[p.curr_token_index];
	p.curr_token = p.tokens[p.curr_token_index];

	p.root = Dict{};
	p.dict_stack = make([dynamic]^Dict, 0, 4);
	append(&p.dict_stack, &p.root);
	return true;
}

parser_destroy :: proc(p: ^Parser) {
	destroy_value :: proc(value: Value) {
		switch v in value {
		case Array:
			for elem in v do destroy_value(elem);
			free(v);

		case Dict:
			for key, value in v do destroy_value(value);
			free(v);
		}
	}

	free(p.tokens);
	for s in p.allocated_strings do free(s);
	free(p.allocated_strings);
	free(p.dict_stack);

	destroy_value(p.root);
}

error :: proc(p: ^Parser, pos: token.Pos, msg: string, args: ...any) {
	fmt.printf_err("%s(%d:%d) Error: ", pos.file, pos.line, pos.column);
	fmt.printf_err(msg, ...args);
	fmt.println_err();

	p.error_count += 1;
}

next_token :: proc(p: ^Parser) -> token.Token {
	p.prev_token = p.curr_token;
	prev := p.prev_token;

	if p.curr_token_index+1 < len(p.tokens) {
		p.curr_token_index += 1;
		p.curr_token = p.tokens[p.curr_token_index];
		return prev;
	}
	p.curr_token_index = len(p.tokens);
	p.curr_token = p.tokens[p.curr_token_index-1];
	error(p, prev.pos, "Token is EOF");
	return prev;
}


allow_token :: proc(p: ^Parser, kind: token.Kind) -> bool {
	if p.curr_token.kind == kind {
		next_token(p);
		return true;
	}
	return false;
}

expect_token :: proc(p: ^Parser, kind: token.Kind) -> token.Token {
	prev := p.curr_token;
	if prev.kind != kind {
		got := prev.lit;
		if got == "\n" do got = ";";
		error(p, prev.pos, "Expected %s, got %s", token.kind_to_string[kind], got);
	}
	next_token(p);
	return prev;
}

expect_operator :: proc(p: ^Parser) -> token.Token {
	prev := p.curr_token;
	switch prev.kind {
	case token.Kind._operator_start+1 .. token.Kind._operator_end:
		// ok
	case:
		error(p, prev.pos, "Expected an operator, got %s", prev.lit);
	}

	next_token(p);
	return prev;
}

fix_advance :: proc(p: ^Parser) {
	for {
		using token.Kind;
		switch t := p.curr_token; t.kind {
		case EOF, Semicolon:
			return;
		}
		next_token(p);
	}
}

copy_value :: proc(value: Value) -> Value {
	switch v in value {
	case Array:
		a := make(Array, len(v));
		for elem, idx in v {
			a[idx] = copy_value(elem);
		}
		return a;
	case Dict:
		d := make(Dict, cap(v));
		for key, val in v {
			d[key] = copy_value(val);
		}
		return d;
	}
	return value;
}

lookup_value :: proc(p: ^Parser, name: string) -> (Value, bool) {
	for i := len(p.dict_stack)-1; i >= 0; i -= 1 {
		d := p.dict_stack[i];
		if val, ok := d[name]; ok {
			return copy_value(val), true;
		}
	}

	return nil, false;
}

parse_operand :: proc(p: ^Parser) -> (Value, token.Pos) {
	using token.Kind;

	tok := p.curr_token;
	switch p.curr_token.kind {
	case Ident:
		next_token(p);
		v, ok := lookup_value(p, tok.lit);
		if !ok do error(p, tok.pos, "Undeclared identifier %s", tok.lit);
		return v, tok.pos;

	case True:
		next_token(p);
		return true, tok.pos;
	case False:
		next_token(p);
		return false, tok.pos;

	case Nil:
		next_token(p);
		return Nil_Value{}, tok.pos;

	case Integer:
		next_token(p);
		return i64(strconv.parse_i128(tok.lit)), tok.pos;

	case Float:
		next_token(p);
		return strconv.parse_f64(tok.lit), tok.pos;

	case String:
		next_token(p);
		return string(tok.lit), tok.pos;

	case Open_Paren:
		expect_token(p, Open_Paren);
		expr, pos := parse_expr(p);
		expect_token(p, Close_Paren);
		return expr, tok.pos;

	case Open_Bracket:
		expect_token(p, Open_Bracket);
		elems := make([dynamic]Value, 0, 4);
		for p.curr_token.kind != Close_Bracket &&
		    p.curr_token.kind != EOF {
			elem, pos := parse_expr(p);
			append(&elems, elem);

			if !allow_token(p, Comma) {
				break;
			}

		}
		expect_token(p, Close_Bracket);
		return Array(elems[..]), tok.pos;

	case Open_Brace:
		expect_token(p, Open_Brace);

    	dict := Dict{};
    	append(&p.dict_stack, &dict);
    	defer pop(&p.dict_stack);

		for p.curr_token.kind != Close_Brace &&
		    p.curr_token.kind != EOF {
		    name_tok := expect_token(p, Ident);
		    name := name_tok.lit;
		    expect_token(p, Assign);
			elem, pos := parse_expr(p);

			if _, ok := dict[name]; ok {
				error(p, name_tok.pos, "Previous declaration of %s in this scope", name);
			} else {
				dict[name] = elem;
			}

			if !allow_token(p, Comma) {
				break;
			}
		}
		expect_token(p, Close_Brace);
		return dict, tok.pos;

	}
	return nil, tok.pos;
}

parse_atom_expr :: proc(p: ^Parser, operand: Value, pos: token.Pos) -> (Value, token.Pos) {
	using token.Kind;
	loop := true;
	for loop {
		switch p.curr_token.kind {
		case Period:
			next_token(p);
			tok := next_token(p);

			switch tok.kind {
			case Ident:
				d, ok := operand.(Dict);
				if !ok || d == nil {
					error(p, tok.pos, "Expected a dictionary");
					operand = nil;
					continue;
				}
				name := tok.lit;
				val, found := d[name];
				if !found {
					error(p, tok.pos, "Field %s not found in dictionary", name);
					operand = nil;
					continue;
				}
				operand = val;
			case:
				error(p, tok.pos, "Expected a selector, got %s", p.curr_token.lit);
				operand = nil;
			}

		case Open_Bracket:
			open := expect_token(p, Open_Bracket);
			index, index_pos := parse_expr(p);
			close := expect_token(p, Close_Bracket);

			a, ok := operand.(Array);
			if ok {
				i, ok := index.(i64);
				if !ok {
					error(p, index_pos, "Index must be an integer for an array");
					operand = nil;
					continue;
				}

				if 0 <= i && i < i64(len(a)) {
					operand = a[i];
				} else {
					error(p, index_pos, "Index %d out of bounds range 0..%d", i, len(a));
					operand = nil;
					continue;
				}
			} else {
				error(p, index_pos, "Indexing is only allowed on an array");
			}

		case:
			loop = false;
		}
	}

	return operand, pos;
}

parse_unary_expr :: proc(p: ^Parser) -> (Value, token.Pos) {
	using token.Kind;
	op := p.curr_token;
	switch p.curr_token.kind {
	case Add, Sub:
		next_token(p);
		// TODO(bill): Calcuate values as you go!
		expr, pos := parse_unary_expr(p);

		switch e in expr {
		case i64: if op.kind == Sub do return -e, pos;
		case f64: if op.kind == Sub do return -e, pos;
		case:
			error(p, op.pos, "Unary operator %s can only be used on integers or floats", op.lit);
			return nil, op.pos;
		}

		return expr, op.pos;

	case Not:
		next_token(p);
		expr, pos := parse_unary_expr(p);
		if v, ok := expr.(bool); ok {
			return !v, op.pos;
		}
		error(p, op.pos, "Unary operator %s can only be used on booleans", op.lit);
		return nil, op.pos;
	}

	return parse_atom_expr(p, parse_operand(p));
}


value_order :: proc(v: Value) -> int {
	switch _ in v {
	case bool, string:
		return 1;
	case i64:
		return 2;
	case f64:
		return 3;
	}
	return 0;
}

match_values :: proc(left, right: ^Value) -> bool {
	if value_order(right^) < value_order(left^) {
		return match_values(right, left);
	}

	switch x in left^ {
	case:
		right^ = left^;
	case bool, string:
		return true;
	case i64:
		switch y in right^ {
		case i64:
			return true;
		case f64:
			left^ = f64(x);
			return true;
		}

	case f64:
		switch y in right {
		case f64:
			return true;
		}
	}

	return false;
}

calculate_binary_value :: proc(p: ^Parser, op: token.Kind, x, y: Value) -> (Value, bool) {
	// TODO(bill): Calculate value as you go!
	match_values(&x, &y);

	using token.Kind;

	switch a in x {
	case: return x, true;

	case bool:
		b, ok := y.(bool);
		if !ok do return nil, false;
		switch op {
		case Eq:    return a == b, true;
		case NotEq: return a != b, true;
		case And:   return a && b, true;
		case Or:    return a || b, true;
		}

	case i64:
		b, ok := y.(i64);
		if !ok do return nil, false;
		switch op {
		case Add:   return a + b, true;
		case Sub:   return a - b, true;
		case Mul:   return a * b, true;
		case Quo:   return a / b, true;
		case Rem:   return a % b, true;
		case Eq:    return a == b, true;
		case NotEq: return a != b, true;
		case Lt:    return a != b, true;
		case Gt:    return a != b, true;
		case LtEq:  return a != b, true;
		case GtEq:  return a != b, true;
		}

	case f64:
		b, ok := y.(f64);
		if !ok do return nil, false;

		switch op {
		case Add:   return a + b, true;
		case Sub:   return a - b, true;
		case Mul:   return a * b, true;
		case Quo:   return a / b, true;
		case Eq:    return a == b, true;
		case NotEq: return a != b, true;
		case Lt:    return a != b, true;
		case Gt:    return a != b, true;
		case LtEq:  return a != b, true;
		case GtEq:  return a != b, true;
		}

	case string:
		b, ok := y.(string);
		if !ok do return nil, false;

		switch op {
		case Add:
			n := len(a) + len(b);
			data := make([]u8, n);
			copy(data[..], cast([]u8)a);
			copy(data[len(a)..], cast([]u8)b);
			s := string(data);
			append(&p.allocated_strings, s);
			return s, true;

		case Eq:    return a == b, true;
		case NotEq: return a != b, true;
		case Lt:    return a != b, true;
		case Gt:    return a != b, true;
		case LtEq:  return a != b, true;
		case GtEq:  return a != b, true;
		}
	}

	return nil, false;
}

parse_binary_expr :: proc(p: ^Parser, prec_in: int) -> (Value, token.Pos) {
	expr, pos := parse_unary_expr(p);
	for prec := token.precedence(p.curr_token.kind); prec >= prec_in; prec -= 1 {
		for {
			op := p.curr_token;
			op_prec := token.precedence(op.kind);
			if op_prec != prec {
				break;
			}
			expect_operator(p);

			if op.kind == token.Kind.Question {
				cond := expr;
				x, x_pos := parse_expr(p);
				expect_token(p, token.Kind.Colon);
				y, y_pos := parse_expr(p);

				if t, ok := cond.(bool); ok {
					expr = t ? x : y;
				} else {
					error(p, pos, "Condition must be a boolean");
				}

			} else {
				right, right_pos := parse_binary_expr(p, prec+1);
				if right == nil {
					error(p, right_pos, "Expected expression on the right-hand side of the binary operator %s", op.lit);
				}
				left := expr;
				ok: bool;
				expr, ok = calculate_binary_value(p, op.kind, left, right);
				if !ok {
					error(p, pos, "Invalid binary operation");
				}
			}
		}
	}
	return expr, pos;
}

parse_expr :: proc(p: ^Parser) -> (Value, token.Pos) {
	return parse_binary_expr(p, 1);
}

expect_semicolon :: proc(p: ^Parser) {
	using token.Kind;

	kind := p.curr_token.kind;

	switch kind {
	case Comma:
		error(p, p.curr_token.pos, "Expected ';', got ','");
		next_token(p);
	case Semicolon:
		next_token(p);
	case EOF:
		// okay
	case:
		error(p, p.curr_token.pos, "Expected ';', got %s", p.curr_token.lit);
		fix_advance(p);
	}
}

parse_assignment :: proc(p: ^Parser) -> bool {
	top_dict :: proc(p: ^Parser) -> ^Dict {
		assert(len(p.dict_stack) > 0);
		return p.dict_stack[len(p.dict_stack)-1];
	}

	using token.Kind;
	if p.curr_token.kind == Semicolon {
		next_token(p);
		return true;
	}
	if p.curr_token.kind == EOF {
		return false;
	}

	tok := p.curr_token;
	if allow_token(p, Ident) {
		expect_token(p, Assign);
		name := tok.lit;
		expr, pos := parse_expr(p);
		d := top_dict(p);
		if _, ok := d[name]; ok {
			error(p, tok.pos, "Previous declaration of %s", name);
		} else {
			d[name] = expr;
		}
		expect_semicolon(p);
		return true;
	}
	error(p, tok.pos, "Expected an assignment, got %s", tok.kind);
	fix_advance(p);
	return false;
}
