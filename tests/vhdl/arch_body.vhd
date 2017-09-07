architecture DataFlow of Full_Adder is
	signal A,B: Bit;
begin
	A <= X xor Y;
	B <= A and Cin;
	Sum <= A xor Cin;
	Cout <= B or (X and Y);
end architecture DataFlow;


architecture Structure of TestBench is
	component C is end component C;
	component Full_Adder
		port (X, Y, Cin: Bit; Cout, Sum: out Bit);
	end component;
	signal A,B,C,D,E,F,G: Bit;
	signal OK: Boolean;
begin
	UUT:        Full_Adder port map (A,B,C,D,E);
	Generator:  AdderTest  port map (A,B,C,F,G);
	Comparator: AdderCheck port map (D,E,F,G,OK);
end Structure;


architecture Behavior of AndGate is begin
	process (Inputs)
		variable Temp: Bit;
	begin
		Temp := '1';
		for i in Inputs'Range loop
			if Inputs(i) = '0' then
				Temp := '0';
				exit;
			end if;
		end loop;
		Result <= Temp after 10 ns;
	end process;
end Behavior;
