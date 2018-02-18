entity foo is end;
architecture bar of foo is
	type BIT is ('0', '1');
	type COMP is record
		a : BIT;
		b : BIT;
	end record;
	procedure prok is begin
		-- name
		X := '0';

		-- positional array aggregate
		(X,Y) := "00";

		-- named array aggregate
		(1 => X, 0 => Y) := "00";

		-- mixed array aggregate
		(X, 1 => Y) := "00";

		-- positional record aggregate
		(X,Y) := Z;

		-- named record aggregate
		(a => X, b => Y) := Z;

		-- mixed record aggregate
		(X, b => Y) := Z;
	end;
begin end;
