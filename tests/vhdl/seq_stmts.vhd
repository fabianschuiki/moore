package body foo is
function bar return std_logic is
begin


-- Wait Statement
wait;
wait for 10 ns;
wait until false;
wait on S;
wait until F(S(3)) and (S(l) or S(r));
wait on S(3), S, l, r until F(S(3)) and (S(l) or S(r));
wait on S(3), S, l, r until F(S(3)) and (S(l) or S(r)) for 20 ns;

--loop
--	wait on Clk;
--	exit when Clk = '1';
--end loop;


-- Assertion Statement
assert (J /= C) report "J = C" severity note;
assert (not OVERFLOW) report "Accumulator overflowed" severity failure;
assert false report "Stack overflow" severity error;
assert D'stable(SETUP_TIME) report "Setup Violation..." severity warning;

assert 3 = 2 + 2;
assert 3 = 2 + 2 report "Assertion violation.";
assert 3 = 2 + 2 report "Assertion violation." severity error;
assert i < 5 report "unexpected value. i = " & integer'image(i);


-- Report Statement
report "Entering process P";
report "Setup or Hold violation; outputs driven to 'X'" severity WARNING;


-- Signal Assignment Statement


-- If Statement
if (X = 5) and (Y = 9) then
	--Z <= A;
elsif (X >= 5) then
	--Z <= B;
else
	--Z < C;
end if;

if RESET = '1' then
	--COUNT <= 0;
elsif CLK'event and CLK = '1' then
	if (COUNT >= 9) then
		--COUNT <= 0;
	else
		--COUNT <= COUNT + 1;
	end if;
end if;


-- Generate Statement
--L1: CELL port map (Top, Bottom, A(0), B(0));
L2: for I in 1 to 3 generate
	L3: for J in 1 to 3 generate
		L4: if I+J>4 generate
			--L5: CELL port map (A(I-1),B(J-1),A(I),B(J));
		end generate;
	end generate;
end generate;

L6: for I in 1 to 3 generate
	L7: for J in 1 to 3 generate
		L8: if I+J<4 generate
			--L9: CELL port map (A(I+1),B(J+1),A(I),B(J));
		end generate;
	end generate;
end generate;

L1: case verify_mode generate
	when V_rtl: all_rtl | cpu_rtl =>
		--CPU1: entity work.cpu(rtl) port map (foo);
	when V_bfm: others =>
			signal bfm_sig : BIT;
		begin
			--CPU1: entity work.cpu(bfm) port map (bar);
	end V_bfm;
end generate L1;

L2: if A1: max_latency < 10 generate
		signal s1 : BIT;
	begin
		--multiplier1: parallel_multiplier port map (foo);
	end A1;
else A2: generate
		signal s1 : STD_LOGIC;
	begin
		--multiplier1: sequential_multiplier port map (bar);
	end A2;
end generate L2;


end;
end;
