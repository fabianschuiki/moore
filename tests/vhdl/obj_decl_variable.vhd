entity foo is end;
architecture bar of foo is
	shared variable INDEX: INTEGER range 0 to 99 := 0;
	shared variable COUNT: POSITIVE;
	shared variable MEMORY: BIT_MATRIX (0 to 7, 0 to 1023);
begin end;
