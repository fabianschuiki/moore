package foo is end;
package foo is end package;
package foo is end package foo;
-- package foo is end package bar;

package foo is
	generic (stuff : INTEGER := 0);
end;

package foo is
	generic (stuff : INTEGER := 0);
	generic map (stuff => 0);
end;

package TimeConstants is
	constant tPLH: Time := 10 ns;
	constant tPHL: Time := 12 ns;
	constant tPLZ: Time := 7 ns;
	constant tPZL: Time := 8 ns;
	constant tPHZ: Time := 8 ns;
	constant tPZH: Time := 9 ns;
end TimeConstants;

package TriState is
	type Tri is ('0', '1', 'Z', 'E');
	function BitVal (Value: Tri) return Bit;
	function TriVal (Value: Bit) return Tri;
	type TriVector is array (Natural range <>) of Tri;
	function Resolve (Sources: TriVector) return Tri;
end package TriState;
