package pkg is
	type MVL is ('0', '1', 'Z', 'X');
	type MVL_Vector is array (Natural range <>) of MVL;

	function "and" (Left, Right: MVL) return MVL;
	function "or" (Left, Right: MVL) return MVL;
	function "not" (Value: MVL) return MVL;
	function "xor" (Right: MVL_Vector) return MVL;
end;

library work;
use work.pkg.all;
entity foo is end;

architecture bar of foo is
	signal Q,R,S,T: MVL;
	signal V: MVL_Vector(0 to 3);
begin
	Q <= 'X' or '1';
	R <= "or" ('0','Z');
	S <= (Q and R) or not S;
	T <= xor V;
end;
