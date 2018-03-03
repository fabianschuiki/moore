entity foo is end;
architecture bar of foo is

	constant xA : std.standard.INTEGER;
	constant xB : INTEGER := -128;
	constant xC : INTEGER := 127;

	constant yA : std.standard.NATURAL;
	constant yB : NATURAL := 0;
	constant yC : NATURAL := 127;

	constant zA : std.standard.POSITIVE;
	constant zB : POSITIVE := 1;
	constant zC : POSITIVE := 127;

begin end;
