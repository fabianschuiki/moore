entity foo is
	port (
		A: in integer;
		B: out integer;
		C: inout integer;
		D: buffer integer
	);
end;

architecture bar of foo is
begin
end;

-- entity @foo_bar (i32 %A, i32 %C) (i32 %B, i32 %C2, i32 %D) {
-- }
