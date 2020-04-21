entity foo is end;
architecture bar of foo is
	type IntegerFile is file of INTEGER;
	file F1: IntegerFile;
	file F2: IntegerFile is "test.dat";
	file F3: IntegerFile open WRITE_MODE is "test.dat";
begin end;
