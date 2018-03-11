package pkg is
	type SMALLINT is range 0 to 3;
	constant two : SMALLINT := 2;
end;

library work;
use work.pkg;
entity foo is end;
architecture bar of foo is
	type BOOLEAN is (false, true);
	type BIT is ('0', '1');
	type BIT2 is ('1', '2');
	--type BIT3 is ('X', '0');
	--type INTEGER is range -256 to 255;
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
	--constant s50 : INTEGER := INTEGER('0');
	constant s51 : INTEGER := INTEGER(123);

	-- primary allocator
	constant s60 : INTEGER := new INTEGER;
	constant s61 : INTEGER := new INTEGER'(123);

	-- primary parenthesized
	constant s70 : INTEGER := (123);
	constant s71 : INTEGER := (s10);

	-- factor
	constant s80 : INTEGER := 2 ** 4;
	constant s81 : INTEGER := abs s00;
	constant s82 : INTEGER := not s00;
	constant s83 : INTEGER := and s00;
	constant s84 : INTEGER := or s00;
	constant s85 : INTEGER := nand s00;
	constant s86 : INTEGER := nor s00;
	constant s87 : INTEGER := xor s00;
	constant s88 : INTEGER := xnor s00;

	-- term
	constant s90 : INTEGER := 2 * 2;
	constant s91 : INTEGER := 8 / 2;
	constant s92 : INTEGER := 8 mod 2;
	constant s93 : INTEGER := 8 rem 2;

	-- simple expression
	constant s100 : INTEGER := -2;
	constant s101 : INTEGER := +2;
	constant s102 : INTEGER := 2 + 2;
	constant s103 : INTEGER := 4 + 2;
	constant s104 : BITS := "00" & "100";

	-- shift expression
	constant s110 : INTEGER := 16 sll 4;
	constant s111 : INTEGER := 16 srl 4;
	constant s112 : INTEGER := 16 sla 4;
	constant s113 : INTEGER := 16 sra 4;
	constant s114 : INTEGER := 16 rol 4;
	constant s115 : INTEGER := 16 ror 4;

	-- relation
	constant s120 : INTEGER := 8 = 4;
	constant s121 : INTEGER := 8 /= 4;
	constant s122 : INTEGER := 8 < 4;
	constant s123 : INTEGER := 8 <= 4;
	constant s124 : INTEGER := 8 > 4;
	constant s125 : INTEGER := 8 >= 4;
	constant s126 : INTEGER := 8 ?= 4;
	constant s127 : INTEGER := 8 ?/= 4;
	constant s128 : INTEGER := 8 ?< 4;
	constant s129 : INTEGER := 8 ?<= 4;
	constant s12A : INTEGER := 8 ?> 4;
	constant s12B : INTEGER := 8 ?>= 4;

	-- logical expression
	constant s130 : INTEGER := '0' and '1';
	constant s131 : INTEGER := '0' or '1';
	constant s132 : INTEGER := '0' xor '1';
	constant s133 : INTEGER := '0' nand '1';
	constant s134 : INTEGER := '0' nor '1';
	constant s135 : INTEGER := '0' xnor '1';

	-- condition
	constant s140 : BOOLEAN := ?? 123;

begin end;
