entity foo is
end;

architecture bar of foo is
begin
	empty : process
	begin
	end process;
end;

-- proc @foo_bar_empty () () {
-- }
--
-- entity @foo_bar () () {
--     %empty = inst @foo_bar_empty () ()
-- }
