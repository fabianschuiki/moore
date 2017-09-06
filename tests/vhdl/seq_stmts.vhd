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


-- Case Statement
case SEL is
	when "01" =>   -- Z <= A;
	when "10" =>   -- Z <= B;
	when others => -- Z <= 'X';
end case;

case INT_A is
	when 0      => -- Z <= A;
	when 1 to 3 => -- Z <= B;
	when 4|6|8  => -- Z <= C;
	when others => -- Z <= 'X';
end case;


-- Loop Statement
for I in o to 3 loop
	if (A = I) then
		--Z(I) <= '1';
	end if;
end loop;

--TMP := '0';
for I in A'low to A'high loop
	--TMP := TMP xor A(I);
end loop;
--ODD <= TMP;

for SEL in PRIMARY loop
	--V_BUS <= VIDEO(SEL);
	wait for 10 ns;
end loop;

--Z <= "0000";
--I := 0;
while (I <= 3) loop
	if (A = I) then
		--Z(I) <= '1';
	end if;
	--I := I + 1;
end loop;

while NOW < MAX_SIM_TIME loop
	--CLK <= not CLK;
	wait for PERIOD/2;
end loop;
wait;

--Z <= "0000";
--I := 0;
L1: loop
	if (A = I) then
		--Z(I) <= '1';
	end if;
	--I := I + 1;
end loop;


-- Next Statement
next;
next foo;
next when I = 4;
next bar when I = 4;


-- Exit Statement
exit;
exit foo;
exit when I = 4;
exit L1 when I = 4;


-- Return Statement
return;
return 123;
return 102 downto 9;


-- Null Statement
null;


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
