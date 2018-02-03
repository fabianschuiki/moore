package pkg is
	type BIT is ('0', '1');
	type range_type is range -100 to 100;
	type range_type_2 is range -10 to 10;

	-- Array subtyping
	type unbounded_array_type is array (range_type range <>) of BIT;
	type constrained_array_type_1 is array (BIT) of BIT;
	type constrained_array_type_2 is array (0 to 10) of BIT;
	type constrained_array_type_3 is array (0 to 10, 0 to 4) of BIT;

	subtype array_subtype_1 is unbounded_array_type (0 to 100);
	--subtype array_subtype_2 is unbounded_array_type (0 to 104); -- should fail
	--subtype array_subtype_3 is constrained_array_type_1 (0 to 2); -- should fail
	subtype array_subtype_4 is constrained_array_type_2 (0 to 3);
	--subtype array_subtype_5 is constrained_array_type_2 (0 to 12); -- should fail
	--subtype array_subtype_6 is constrained_array_type_3 (0 to 4, open); -- should fail
	--subtype array_subtype_7 is constrained_array_type_3 (open, 0 to 1); -- should fail
	subtype array_subtype_8 is constrained_array_type_3 (0 to 4, 0 to 1);
	subtype array_subtype_9 is unbounded_array_type (range_type_2);
	--subtype array_subtype_10 is constrained_array_type_3 (0 to 4); -- should fail

	-- Record subtyping
	--type record_type is record
	--	a : range_type;
	--	b : range_type;
	--end record;

	--subtype record_subtype_1 is record_type;
	--subtype record_subtype_2 is record_type (a(0 to 10), b(10 to 20));
	--subtype record_subtype_3 is record_type (a(-10 to 10));
	--subtype record_subtype_4 is record_type (b(0 to 105)); -- should fail
end;

library work;
use work.pkg.all;
entity foo is end;

architecture bar of foo is
	-- Currently the architecture is required to trigger typeck of the entire
	-- library.
begin end;

-- @ elab foo(bar)
