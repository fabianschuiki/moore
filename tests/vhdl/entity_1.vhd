entity foo is
	port (
		A: in integer;
		B,C: out integer;
		D: inout integer;
		E: buffer integer
	);
end;

architecture bar of foo is
begin
end;

-- entity @foo_bar (i32 %A, i32 %D) (i32 %B, i32 %C, i32 %D0, i32 %E) {
-- }
