package pkg is
	type small is range 0 to 7;
end;

library work; -- should be optional

entity foo is
	port(A: work.pkg.small);
end;

architecture bar of foo is
begin
end;
