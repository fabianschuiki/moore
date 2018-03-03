entity foo is end;
architecture bar of foo is

	constant A : std.standard.FILE_OPEN_STATUS;
	constant B : FILE_OPEN_STATUS := OPEN_OK;
	constant C : FILE_OPEN_STATUS := STATUS_ERROR;
	constant D : FILE_OPEN_STATUS := NAME_ERROR;
	constant E : FILE_OPEN_STATUS := MODE_ERROR;

begin end;
