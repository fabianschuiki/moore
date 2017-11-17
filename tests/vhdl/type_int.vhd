package pkg is
	type TWOS_COMPLEMENT_INTEGER is range -32768 to 32767;
	type BYTE_LENGTH_INTEGER is range 0 to 255;
	type WORD_INDEX is range 31 downto 0;
	subtype HIGH_BIT_LOW is BYTE_LENGTH_INTEGER range 0 to 127;
end;

library work;
use work.pkg.all;
entity foo is end;

architecture bar of foo is
	signal a0 : TWOS_COMPLEMENT_INTEGER; -- should be initialized to -32768
	signal a1 : TWOS_COMPLEMENT_INTEGER := 0;
	signal a2 : TWOS_COMPLEMENT_INTEGER := -42;
	signal a3 : TWOS_COMPLEMENT_INTEGER := 42;

	signal b0 : BYTE_LENGTH_INTEGER; -- should be initialized to 0
	signal b1 : BYTE_LENGTH_INTEGER := 0;
	signal b2 : BYTE_LENGTH_INTEGER := 42;

	signal c0 : WORD_INDEX; -- should be initialized to 31
	signal c1 : WORD_INDEX := 0;
	signal c2 : WORD_INDEX := 21;

	signal d0 : HIGH_BIT_LOW; -- should be initialized to 0
	signal d1 : HIGH_BIT_LOW := 0;
	signal d2 : HIGH_BIT_LOW := 42;

	signal e0 : TWOS_COMPLEMENT_INTEGER range 0 to 3; -- should be initialized to 0
	signal e1 : TWOS_COMPLEMENT_INTEGER range 0 to 3 := 3;

	signal f0 : TWOS_COMPLEMENT_INTEGER range 8 to 7;
begin end;

--@ +elab foo(bar)

--| entity @foo_bar () () {
--|     %a0 = sig i16 -32768
--|     %a1 = sig i16 0
--|     %a2 = sig i16 -42
--|     %a3 = sig i16 42
--|     %b0 = sig i8 0
--|     %b1 = sig i8 0
--|     %b2 = sig i8 42
--|     %c0 = sig i5 31
--|     %c1 = sig i5 0
--|     %c2 = sig i5 21
--|     %d0 = sig i7 0
--|     %d1 = sig i7 0
--|     %d2 = sig i7 42
--|     %e0 = sig i2 0
--|     %e1 = sig i2 3
--|     %f0 = sig void void
--| }
