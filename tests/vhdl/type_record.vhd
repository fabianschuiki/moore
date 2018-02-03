package pkg is
	type BIT is ('0','1');
	type INTEGER is range -2147483648 to 2147483647;
	type SIGNED_FXPT is array (INTEGER range <>) of BIT;
	type MONTH_NAME is (JAN, FEB, MAR, APR, MAY, JUN, JUL, AUG, SEP, OCT, NOV, DEC);

	type DATE is record
		DAY   : INTEGER range 1 to 31;
		MONTH : MONTH_NAME;
		YEAR  : INTEGER range 0 to 4000;
	end record;

	type SIGNED_FXPT_COMPLEX is record
		RE : SIGNED_FXPT;
		IM : SIGNED_FXPT;
	end record;
end;

library work;
use work.pkg.all;
entity foo is end;

architecture bar of foo is
	signal a0: DATE;

	signal b0: SIGNED_FXPT_COMPLEX;
	--signal b1: SIGNED_FXPT_COMPLEX (RE(4 downto -16), IM(4 downto -12));
	--signal b2: SIGNED_FXPT_COMPLEX (RE(-16 downto 4), IM(4 downto -12));
	--signal b3: SIGNED_FXPT_COMPLEX (RE(4 downto -16), IM(-12 downto 4));
begin end;

--@elab foo(bar)

--| entity @foo_bar () () {
--|     %a0 = sig {i5, n12, i12} {1, 0, 0}
--|     %b0 = sig {[21 x n2], [17 x n2]} {[.. 0], [.. 0]}
--|     %b1 = sig {void, [17 x n2]} {void, [.. 0]}
--|     %b2 = sig {[21 x n2], void} {[.. 0], void}
--| }
