package pkg is
	type MULTI_LEVEL_LOGIC is (LOW, HIGH, RISING, FALLING, AMBIGUOUS);
	type BIT is ('0', '1');
	type SWITCH_LEVEL is ('0', '1', 'X');
	type MIXED is ('0', '1', SOME_OTHER);
end;

library work;
use work.pkg.all;
entity foo is end;

architecture bar of foo is
	signal a0 : MULTI_LEVEL_LOGIC; -- should be initialized to LOW
	signal a1 : MULTI_LEVEL_LOGIC := LOW;
	signal a2 : MULTI_LEVEL_LOGIC := HIGH;
	signal a3 : MULTI_LEVEL_LOGIC := RISING;
	signal a4 : MULTI_LEVEL_LOGIC := FALLING;
	signal a5 : MULTI_LEVEL_LOGIC := AMBIGUOUS;

	signal b0 : BIT; -- should be initialized to '0'
	signal b1 : BIT := '0';
	signal b2 : BIT := '1';

	signal c0 : SWITCH_LEVEL; -- should be initialized to '0'
	signal c1 : SWITCH_LEVEL := '0';
	signal c2 : SWITCH_LEVEL := '1';
	signal c3 : SWITCH_LEVEL := 'X';

	signal d0 : MIXED; -- should be initialized to '0'
	signal d1 : MIXED := '0';
	signal d2 : MIXED := '1';
	signal d3 : MIXED := SOME_OTHER;
begin end;

-- @ elab foo(bar)

--| entity @foo_bar () () {
--|     %a0 = sig n5 0
--|     %a1 = sig n5 0
--|     %a2 = sig n5 1
--|     %a3 = sig n5 2
--|     %a4 = sig n5 3
--|     %a5 = sig n5 4
--|     %b0 = sig n2 0
--|     %b1 = sig n2 0
--|     %b2 = sig n2 1
--|     %c0 = sig n3 0
--|     %c1 = sig n3 0
--|     %c2 = sig n3 1
--|     %c3 = sig n3 2
--|     %d0 = sig n3 0
--|     %d1 = sig n3 0
--|     %d2 = sig n3 1
--|     %d3 = sig n3 2
--| }
