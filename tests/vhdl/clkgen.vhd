package pkg is
	type BIT is range 0 to 1;
end package;

library work;
use work.pkg;

entity clkgen is
	port (CK: out pkg.BIT);
end;

architecture behav of clkgen is
begin
	p_clkgen: process
	begin
		CK <= 0;
		wait for 10 ns;
		for I in 0 to 3 loop
			CK <= 1;
			wait for 5 ns;
			CK <= 0;
			wait for 5 ns;
		end loop;
	end process;
end;
