entity foo is end;
architecture bar of foo is

	constant A : std.standard.FILE_OPEN_KIND;
	constant B : FILE_OPEN_KIND := READ_MODE;
	constant C : FILE_OPEN_KIND := WRITE_MODE;
	constant D : FILE_OPEN_KIND := APPEND_MODE;

begin end;
