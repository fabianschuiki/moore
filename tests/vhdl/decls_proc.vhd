-- This file tests block declarative items.
entity foo is end;
architecture bar of foo is
begin
	process is
		type BIT is ('0', '1');

		-- subprogram_declaration
		procedure proc_a;
		function func_a return BIT;

		-- subprogram_body
		procedure proc_a is begin
		end;
		function func_a return BIT is begin
		end;

		-- subprogram_instantiation_declaration
		--procedure proc_b is new proc_a;
		--function func_b is new func_a;

		-- package_declaration
		package pkg_a is end;

		-- package_body
		package body pkg_a is end;

		-- package_instantiation_declaration
		package pkg_b is new pkg_a;

		-- type_declaration
		type NUM is range 0 to 100;

		-- subtype_declaration
		subtype ANS is NUM range 0 to 42;

		-- constant_declaration
		--constant const_a : BIT;

		-- variable_declaration
		--variable shvar_a : BIT;

		-- file_declaration
		--file file_a : BIT;

		-- alias_declaration
		--alias alias_a is pkg_a;

		-- attribute_declaration
		--attribute attr_a : BIT;

		-- attribute_specification
		--attribute attr_a of NUM : type is '0';

		-- use_clause
		use work.pkg.all;

		-- group_template_declaration
		--group grp_tmp_a is (signal, signal);

		-- group_declaration
		--group grp_a : grp_tmp_a (sig_a, sig_a);
	begin end process;
end;

-- @elab foo
