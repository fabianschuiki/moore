entity foo is end;
architecture bar of foo is
	type BIT is ('0', '1');
	procedure prok is begin
		case 0 is
			-- expression
			when 1 => null;
			when not 3 => null;

			-- discrete range
			when 0 to 4 => wait;
			when bit => wait;

			-- element name
			when asdf => null;

			-- others
			when others => null;
		end case;
	end;
begin end;
