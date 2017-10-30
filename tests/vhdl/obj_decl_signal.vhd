entity foo is end;
architecture bar of foo is
	signal S: STANDARD.BIT_VECTOR (1 to 10);
	signal CLK1, CLK2: TIME;
	signal CLK3: TIME register;
	signal CLK4: TIME bus;
	signal X: INTEGER := 42;
	signal OUTPUT: WIRED_OR MULTI_VALUED_LOGIC;
begin end;
