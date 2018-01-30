entity foo is
end;

architecture bar of foo is
	type bit is ('0','1');
	type index is range 3 downto 0;
	type bits is array (index) of bit;
	signal a : bits;
	--signal c : bits;
begin
	stim : process
	begin
		a <= (others => '0');
		a <= "0000";
		--a <= 0;
		--b <= 0;
		----c(7 downto 0) <= 0;
		----(a, b) <= (0, 0);

		---- simple assignment
		--a <= 0;
		--a <= 0 after 10 ns;
		--a <= null;
		--a <= null after 10 ns;

		--a <= unaffected;
		--a <= 0, 1;

		--a <= transport 0;
		--a <= inertial 0;
		--a <= reject 10 ns inertial 0;

		--a <= force in 0;
		--a <= force out 0;

		--a <= release in;
		--a <= release out;

		-- conditional assignment

		-- selected assignment
	end process;
end;
