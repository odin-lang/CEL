import "cel.odin";
import "token.odin";

sample := `
x = 123;
y = 321.456;
z = x * (y - 1) / 2;
w = "foo" + "bar";

# This is a comment

asd = "Semicolons are optional"

a = {id = {b = 123}} # Dict
b = a.id.b

f = [1, 4, 9] # Array
g = f[2]

h = x < y and w == "foobar"
i = h ? 123 : "google"

j = nil
`;


main :: proc() {
	t: token.Tokenizer;
	token.init(&t, cast([]u8)sample);

	p: cel.Parser;
	if ok := cel.parser_init(&p, &t); !ok {
		return;
	}
	defer cel.parser_destroy(&p);

	for p.curr_token.kind != token.Kind.EOF &&
	    p.curr_token.kind != token.Kind.Illegal &&
	    p.curr_token_index < len(p.tokens) {
		if !cel.parse_assignment(&p) {
			break;
		}
	}

	if p.error_count == 0 {
		cel.print(&p);
	}
}
