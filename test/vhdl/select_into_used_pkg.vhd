package pkg is
	type BIT is range 0 to 1;
end package;

library work;
use work.pkg;

entity A is
	port (CK: out pkg.BIT);
	--            ^^^ this fails at the moment
end;

architecture empty of A is begin end;
