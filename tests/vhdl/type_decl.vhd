package foo is
	-- enum_type_def
	type foo;
	type MULTI_LEVEL_LOGIC is (LOW, HIGH, RISING, FALLING, AMBIGUOUS);
	type BIT is ('0','1');
	type SWITCH_LEVEL is ('0','1','X');

	-- integer_type_def
	type TWOS_COMPLEMENT_INTEGER is range -32768 to 32767;
	type BYTE_LENGTH_INTEGER is range 0 to 255;
	type WORD_INDEX is range 31 downto 0;

	-- floating_type_def
	type bubba is range -1E18 to 1E18;

	-- physical_type_def
	type DURATION is range -1E18 to 1E18
		units
			fs;
			ps    = 1000 fs;
			ns    = 1000 ps;
			us    = 1000 ns;
			ms    = 1000 us;
			sec   = 1000 ms;
			min   = 60 sec;
		end units;
	type DISTANCE is range 0 to 1E16
		units
			-- primary unit:
			Å;
			-- metric lengths:
			nm   = 10 Å;
			um   = 1000 nm;
			mm   = 1000 um;
			cm   = 10 mm;
			m    = 1000 mm;
			km   = 1000 m;
			-- English lengths:
			mil  = 254000 Å;
			inch = 1000 mil;
			ft   = 12 inch;
			yd   = 3 ft;
			fm   = 6 ft;
			mi   = 5280 ft;
			lg   = 3 mi;
		end units DISTANCE;

	-- array_type_def
	type MY_WORD is array (0 to 31) of BIT;
	type DATA_IN is array (7 downto 0) of FIVE_LEVEL_LOGIC;
	type MEMORY is array (INTEGER range <>) of MY_WORD;
	type SIGNED_FXPT is array (INTEGER range <>) of BIT;
	type SIGNED_FXPT_VECTOR is array (NATURAL range <>) of SIGNED_FXPT;
	type SIGNED_FXPT_5x4 is array (1 to 5, 1 to 4) of SIGNED_FXPT;
	type Word is array (NATURAL range <>) of BIT;
	type Memory is array (NATURAL range <>) of Word (31 downto 0);
	type E is array (NATURAL range <>) of INTEGER;
	type T is array (1 to 10) of E (1 to 0);

	-- record_type_def
	type DATE is record
			DAY : INTEGER range 1 to 31;
			MONTH : MONTH_NAME;
			YEAR : INTEGER range 0 to 4000;
		end record;
	type SIGNED_FXPT_COMPLEX is record
			RE : SIGNED_FXPT;
			IM : SIGNED_FXPT;
		end record;

	-- access_type_def
	type ADDRESS is access MEMORY;
	type BUFFER_PTR is access TEMP_BUFFER;

	-- file_type_def
	type A is file of STRING;
	type B is file of NATURAL;
end;
