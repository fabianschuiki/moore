package pkg is
	type SMALLINT is range 0 to 3;
	constant two : SMALLINT := 2;
end;

library work;
use work.pkg;
entity foo is end;
architecture bar of foo is
	--type BOOLEAN is (false, true);
	--type BIT is ('0', '1');
	--type BIT2 is ('1', '2');
	--type BIT3 is ('X', '0');
	--type INTEGER is range -256 to 255;
	--type BIT_VECTOR is array (INTEGER range <>) of BIT;
	subtype TRIBITS is BIT_VECTOR (0 to 2);
	subtype PENTABITS is BIT_VECTOR (0 to 4);
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
	--constant s02 : BIT_VECTOR(0 to 4) := "00100";

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
	constant s82 : TRIBITS := not s23;
	constant s83 : TRIBITS := and s23;
	constant s84 : TRIBITS := or s23;
	constant s85 : TRIBITS := nand s23;
	constant s86 : TRIBITS := nor s23;
	constant s87 : TRIBITS := xor s23;
	constant s88 : TRIBITS := xnor s23;

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
	constant s104 : BIT_VECTOR := "00" & "100";

	-- shift expression
	constant s110 : TRIBITS := s23 sll 4;
	constant s111 : TRIBITS := s23 srl 4;
	constant s112 : TRIBITS := s23 sla 4;
	constant s113 : TRIBITS := s23 sra 4;
	constant s114 : TRIBITS := s23 rol 4;
	constant s115 : TRIBITS := s23 ror 4;

	-- relation
	constant s120 : INTEGER := 8 = 4;
	constant s121 : INTEGER := 8 /= 4;
	constant s122 : INTEGER := 8 < 4;
	constant s123 : INTEGER := 8 <= 4;
	constant s124 : INTEGER := 8 > 4;
	constant s125 : INTEGER := 8 >= 4;
	constant s126 : BIT := '0' ?= '1';
	constant s127 : BIT := '0' ?/= '1';
	constant s128 : BIT := s23 ?= s23;
	constant s129 : BIT := s23 ?/= s23;
	constant s12A : BIT := '0' ?< '1';
	constant s12B : BIT := '0' ?<= '1';
	constant s12C : BIT := '0' ?> '1';
	constant s12D : BIT := '0' ?>= '1';

	-- logical expression
	constant s130 : BIT := '0' and '1';
	constant s131 : BIT := '0' or '1';
	constant s132 : BIT := '0' xor '1';
	constant s133 : BIT := '0' nand '1';
	constant s134 : BIT := '0' nor '1';
	constant s135 : BIT := '0' xnor '1';

	-- condition
	constant s140 : BOOLEAN := ?? 123;

begin end;
