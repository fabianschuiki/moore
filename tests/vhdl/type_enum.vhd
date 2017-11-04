package pkg is
	type MULTI_LEVEL_LOGIC is (LOW, HIGH, RISING, FALLING, AMBIGUOUS);
	type BIT is ('0','1');
	type SWITCH_LEVEL is ('0','1','X');
end;

library work;
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
begin end;

--@ +elab foo(bar)

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
--| }
