package gen1_pkg is
	generic (type element_type);
	type ptr is access element_type;
end;

package gen2_pkg is
	generic (value : integer);
	constant konst : integer := value;
end;

package comb_pkg is
	generic (
		type element_type;
		value : integer
	);
	package p1 is new gen1_pkg generic map (element_type => element_type);
	package p2 is new gen2_pkg generic map (value => value);
end;

package root_pkg is
	type foo is access integer;
	constant bar : integer := 42;
	package inst1_pkg is new gen1_pkg generic map (element_type => string);
	package inst2_pkg is new gen2_pkg generic map (value => 42);
end;


use work.root_pkg.foo, work.root_pkg.bar;
entity e1 is
	type out_foo is access foo;
	constant out_bar : integer := bar;
end;

use work.root_pkg.inst1_pkg.ptr, work.root_pkg.inst2_pkg.konst;
entity e2 is
	type out_ptr is access ptr;
	constant out_konst : integer := konst;
end;

use work.all;
entity e3 is
	package p1a is new gen1_pkg generic map (element_type => integer);
	package p1b is new gen1_pkg generic map (element_type => string);
	package p2a is new gen2_pkg generic map (value => 42);
	package p2b is new gen2_pkg generic map (value => 99);
end;

architecture empty of e3 is
begin
end architecture;
