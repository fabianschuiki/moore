-- @elab pkg_a
package pkg_a is
end package;

-- @ elab pkg_b
package pkg_b is
	type BYTE is range 0 to 255;
	type BOOLEAN is (FALSE, TRUE);
	type LOGIC is ('U', 'X', '0', '1');
	constant K : BYTE;
end package;

-- @ elab pkg_c
package pkg_c is
	use work.pkg_b.BYTE;
	type SHORT is range 0 to 65535;
	type INT is range 0 to 4294967295;
	constant K0 : BYTE;
	constant K1 : SHORT;
	constant K2 : INT;
end package;

package pkg_d is
	type TIME is range 1E18 to 1E18 units
		sec;
		min = 60 sec;
		hr  = 60 min;
	end units;
end package;
