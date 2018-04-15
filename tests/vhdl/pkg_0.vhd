-- @elab pkg_a
package pkg_a is
end package;

-- @ elab pkg_b
package pkg_b is
	type BYTE is range 0 to 255;
	constant K : BYTE;
end package;

-- @ elab pkg_c
package pkg_c is
	type BYTE is range 0 to 255;
	type SHORT is range 0 to 65535;
	type INT is range 0 to 4294967295;
	constant K0 : BYTE;
	constant K1 : SHORT;
	constant K2 : INT;
end package;

package pkg_d is
	type DOUGLAS is range 0 to 42;
	package subpkg_a is
		type BOOL is range 0 to 1;
	end package;
end package;
