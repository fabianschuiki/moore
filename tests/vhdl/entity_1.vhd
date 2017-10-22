library std;

entity foo is
	port (
		A:   in     std.standard.integer;
		B,C: out    std.standard.integer;
		D:   inout  std.standard.integer;
		E:   buffer std.standard.integer
	);
end;

architecture bar of foo is
begin
end;

-- entity @foo_bar (i32 %A, i32 %D) (i32 %B, i32 %C, i32 %D0, i32 %E) {
-- }
