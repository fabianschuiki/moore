package pkg is
	type BIT is ('0','1');
	type FIVE_LEVEL_LOGIC is (LOW, HIGH, RISING, FALLING, AMBIGUOUS);
	type INTEGER is range -2147483648 to 2147483647;
	type NATURAL is range 0 to 4294967295;

	type MY_WORD is array (0 to 31) of BIT;                             -- fully constrained
	type BITMAP is array(BIT) of FIVE_LEVEL_LOGIC;
	type DATA_IN is array (7 downto 0) of FIVE_LEVEL_LOGIC;             -- fully constrained
	type MEMORY is array (INTEGER range <>) of MY_WORD;                 -- partially constrained
	type SIGNED_FXPT is array (INTEGER range <>) of BIT;                -- unconstrained
	type SIGNED_FXPT_VECTOR is array (NATURAL range <>) of SIGNED_FXPT; -- unconstrained
	type SIGNED_FXPT_5x4 is array (1 to 5, 1 to 4) of SIGNED_FXPT;      -- partially constrained
	type MEMORY2 is array (INTEGER range 0 to 18) of MY_WORD;

	type E is array (NATURAL range <>) of INTEGER;
	--type T0 is array (1 to 10) of E (1 to 0);
	--type T1 is array (10 to 1) of E (0 to 1);
	--type T2 is array (1 to 10) of E (0 to 1) range 0 to 10;
	--type T3 is array (1 to 10) of E (open);
	--type T4 is array (1 to 10) of E (open) range 0 to 32;
end;

library work;
use work.pkg.all;
entity foo is end;

architecture bar of foo is
	--signal a: DATA_IN;
	--signal b: MEMORY (0 to 255);
	--signal c: SIGNED_FXPT (3 downto -4);
	--signal d: SIGNED_FXPT_VECTOR (1 to 20)(9 downto 0);
	--signal e: SIGNED_FXPT_5x4 (open)(3 downto -4);
	--signal f0: T0;
	--signal f1: T1;
begin end;

-- @elab foo(bar)

--| entity @foo_bar () () {
--|     %a = sig [8 x n5] [.. 0]
--|     %b = sig [256 x [32 x n2]] [.. [.. 0]]
--|     %c = sig [8 x n2] [.. 0]
--|     %d = sig [20 x [10 x n2]] [.. [.. 0]]
--|     %e = sig [5 x [4 x [8 x n2]]] [.. [.. [.. 0]]]
--|     %f0 = sig [10 x void] [.. void]
--|     %f1 = sig void void
--| }
