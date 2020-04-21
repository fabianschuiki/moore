entity foo is end;
architecture bar of foo is

	constant xA : std.standard.BOOLEAN;
	constant xB : BOOLEAN := FALSE;
	constant xC : BOOLEAN := TRUE;

	constant yA : std.standard.BOOLEAN_VECTOR;
	constant yB : BOOLEAN_VECTOR(0 to 1) := (FALSE, TRUE);

begin end;
