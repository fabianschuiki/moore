package foo is
	-- Declaration
	attribute LOCATION: COORDINATE;
	attribute PIN_NO: POSITIVE;

	-- Specification
	attribute PIN_NO of CIN: signal is 10;
	attribute PIN_NO of COUT: signal is 5;
	attribute LOCATION of ADDER1: label is (10,15);
	attribute LOCATION of others: label is (25,77);
	attribute CAPACITANCE of all: signal is 15 pF;
	attribute IMPLEMENTATION of G1: group is "74LS152";
	attribute RISING_DELAY of C2Q: group is 7.2 ns;

	attribute FOREIGN of F: function is "implementation-dependent information";
	--attribute BuiltIn of "or" [MVL, MVL return MVL]: function is TRUE;
	--attribute Mapping of JMP [return OpCode] :literal is "001";
end;
