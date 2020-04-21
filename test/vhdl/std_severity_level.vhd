entity foo is end;
architecture bar of foo is

	constant A : std.standard.SEVERITY_LEVEL;
	constant B : SEVERITY_LEVEL := NOTE;
	constant C : SEVERITY_LEVEL := WARNING;
	constant D : SEVERITY_LEVEL := ERROR;
	constant E : SEVERITY_LEVEL := FAILURE;

begin end;
