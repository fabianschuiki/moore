package pkg is
	type INTEGER is range -2147483648 to 2147483647;
	type MY_FILE is file of INTEGER;
end;

library work;
use work.pkg.all;
entity foo is end;

architecture bar of foo is
begin end;

-- @elab foo(bar)
