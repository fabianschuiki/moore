entity foo is
end;

architecture bar of foo is
	type bit is range 0 to 1;
	signal a : bit;
begin
	stim : process
	begin
		a <= 0;
		a <= 1 after 10 ns;
		--a <= 0 after 0; -- this should be a type error
	end process;
end;
