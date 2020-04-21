configuration bar of stuff is end;

configuration Different of Half_Adder is
	for Structure
		for L1: XOR_GATE
			generic map (2.9 ns, 3.6 ns);
		end for;
		for L2: AND_GATE
			generic map (2.8 ns, 3.25 ns)
			port map (I2 => Tied_High);
		end for;
	end for;
end configuration Different;

architecture Structure of Half_Adder is
	for L1: XOR_GATE use
		entity WORK.XOR_GATE(Behavior)
			generic map (3 ns, 3 ns)
			port map (I1 => I1, I2 => I2, O => O);
	for L2: AND_GATE use
		entity WORK.AND_GATE(Behavior)
			generic map (3 ns, 4 ns)
			port map (I1, open, O);
begin
end architecture Structure;
