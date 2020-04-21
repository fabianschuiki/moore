-- Codegen test
entity e0 is
end entity e0;
architecture demo of e0 is
begin
	process is
	begin
		report "message";
		wait;
	end process;

	report "message"; -- error
end architecture demo;
