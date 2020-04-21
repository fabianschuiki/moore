package foo is
	group G1: RESOURCE (L1, L2);             -- A group of two labels.
	group G2: RESOURCE (L3, L4, L5);         -- A group of three labels.
	group C2Q: PIN2PIN (PROJECT.GLOBALS.CK, Q);
	                                         --  Groups may associate named
	                                         --  entities in different declarative
	                                         --  parts (and regions).
	group CONSTRAINT1: DIFF_CYCLES (G1, G3); -- A group of groups.
end;
