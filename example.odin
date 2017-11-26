import "cel.odin";
import "token.odin";

sample := `
x = 123;
y = 321.456;
z = x * (y - 1) / 2;
w = "foo" + "bar";

# This is a comment

asd = "Semicolons are optional"

a = {id = {b = 123, c = false}} # Dict
b = a.id.b

f = [1, 4, 9] # Array
g = f[2]

h = x < y and w == "foobar"
i = h ? 123 : "google"

j = nil

"127.0.0.1" = "value" # Keys can be strings

"foo" = {
	bar = {
		"baz" = 123 # optional commas if newline is present
		"zab" = 456
		"abz" = "I'm a string,\tJos\u00e9."
	}
}
`;


main :: proc() {
	p, ok := cel.create_from_string(sample);
	if !ok {
		return;
	}
	defer cel.destroy(p);

	if p.error_count == 0 {
		cel.print(p);
	}
}
