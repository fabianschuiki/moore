package pkg is
	type SMALLINT is range 0 to 3;
	constant two : SMALLINT := 2;
end;

library work;
use work.pkg;
entity foo is end;
architecture bar of foo is
	type BIT is ('0', '1');
	type BIT2 is ('1', '2');
	--type BIT3 is ('X', '0');
	type INTEGER is range 0 to 255;
	type BITS is array (INTEGER range <>) of BIT;
	subtype TRIBITS is BITS (0 to 2);
	type REC is record
		a : BIT;
		b : BIT;
		c : BIT;
	end record;

	--attribute STUFF : BIT;
	--attribute STUFF of BIT : type is '0';

	-- primary literal
	constant s00 : INTEGER := 123;
	constant s01 : BIT := '0';
	--constant s02 : BITS := "00100";

	-- primary name
	constant s10 : INTEGER := s00;
	--constant s11 : BIT := BIT'STUFF;
	constant s12 : INTEGER := pkg.two;

	-- primary aggregate
	constant s20 : REC := ('0', '1', '0');
	constant s21 : REC := (a => '0', b => '1', c => '0');
	constant s22 : REC := ('0', c => '0', b => '1');
	constant s23 : TRIBITS := ('0', '1', '0');
	constant s24 : TRIBITS := (0 => '0', 1 => '1', 2 => '0');
	constant s25 : TRIBITS := ('0', 2 => '1', 1 => '0');

	-- primary function call
	constant s30 : INTEGER := square(2);

	-- primary qualified expression
	constant s40 : INTEGER := INTEGER'(123);
	constant s41 : REC := REC'('0', '1', '0');
	constant s42 : REC := REC'(a => '0', b => '1', c => '0');
	constant s43 : REC := REC'('0', c => '0', b => '1');
	constant s44 : TRIBITS := TRIBITS'('0', '1', '0');
	constant s45 : TRIBITS := TRIBITS'(0 => '0', 1 => '1', 2 => '0');
	constant s46 : TRIBITS := TRIBITS'('0', 2 => '1', 1 => '0');

	-- primary type conversion
	constant s50 : INTEGER := INTEGER('0');
	constant s51 : INTEGER := INTEGER(123);

	-- primary allocator
	constant s60 : INTEGER := new INTEGER;
	constant s61 : INTEGER := new INTEGER'(123);

	-- primary parenthesized
	constant s70 : INTEGER := (123);
	constant s71 : INTEGER := (s10);
begin end;
