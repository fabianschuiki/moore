entity foo is end;
architecture bar of foo is

	type BIT is ('0', '1');

	function F1 return BIT is
		--variable X : BIT;
	begin
		wait;
		--X := '0';
		--return X;
	end;

begin end;
