package pkg is
	type BIT is ('0','1');
	type INTEGER is range -2147483648 to 2147483647;
	type MY_WORD is array (0 to 31) of BIT;
	type MEMORY is array (INTEGER range <>) of MY_WORD;

	type ADDRESS is access MEMORY;
	type BUFFER_PTR is access MY_WORD;
end;

library work;
entity foo is end;

architecture bar of foo is
	constant a0: ADDRESS;
	constant b0: BUFFER_PTR;
begin end;

--@ +elab foo(bar)

--| entity @foo_bar () () {
--|     %a0 = sig [0 x [32 x n2]]* null
--|     %b0 = sig [32 x n2]* null
--| }
