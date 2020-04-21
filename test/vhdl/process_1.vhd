entity foo is
end;

architecture bar of foo is
	type bit is range 0 to 1;
	signal a : bit;
begin
	toggle : process
	begin
		a <= 0;
		a <= 1;
	end process;
end;

--@ +elab foo(bar)

--| proc @foo_bar_toggle () (i1$ a) {
--|     drv %a 0
--|     drv %a 1
--| }
--|
--| entity @foo_bar () () {
--|     %a = sig i1 0
--|     %toggle = inst @foo_bar_toggle () (i1$ %a)
--| }
