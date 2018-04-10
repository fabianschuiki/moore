-- @elab pkg_a
package pkg_a is
end package;

-- @ elab pkg_b
package pkg_b is
	type BYTE is range 0 to 255;
	constant K : BYTE;
end package;
