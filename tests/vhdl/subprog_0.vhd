entity foo is end;
architecture bar of foo is

	type BIT is ('0', '1');

	function F1 return BIT is
		--variable X : BIT;
	begin
		wait;
		wait for blah;
		wait until false;
		wait for 10 ns;

		assert false;
		assert false report "holy moly";
		assert false severity warning;
		assert false report "explosion" severity error;

		report "hello";
		report "hello" severity warning;

		--F1(x);
		--Image(x);

		if true then
			wait;
		elsif false then
			wait;
		else
			wait;
		end if;

		case 123 is
			when 1 => wait;
			when 2|3 => wait;
			when 4 to 10 => wait;
			when asdf => wait;
			when others => wait;
		end case;

		while true loop
			wait;
		end loop;

		for x in 0 to 31 loop
			wait;
		end loop;

		--X := '0';
		--return X;
	end;

begin end;
