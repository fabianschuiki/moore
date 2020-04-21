entity foo is end;
architecture bar of foo is

	constant A : std.standard.BIT;
	constant B : BIT := '0';
	constant C : BIT := '1';

	constant xA : std.standard.BIT_VECTOR;
	constant xB : BIT_VECTOR(0 to 1) := ('0', '1');

begin end;
