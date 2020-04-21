entity foo is end;
architecture bar of foo is
	type TIME is range -1E18 to 1E18 units
		fs;
		ps  = 1000 fs;
		ns  = 1000 ps;
		us  = 1000 ns;
		ms  = 1000 us;
		sec = 1000 ms;
		min = 60 sec;
		hr  = 60 min;
	end units;

	type DISTANCE is range 0 to 1E16 units
		Å;

		nm   = 10 Å;
		um   = 1000 nm;
		mm   = 1000 um;
		cm   = 10 mm;
		m    = 1000 mm;
		km   = 1000 m;

		mil  = 254000 Å;
		inch = 1000 mil;
		ft   = 12 inch;
		yd   = 3 ft;
		fm   = 6 ft;
		mi   = 5280 ft;
		lg   = 3 mi;
	end units;

	constant t : TIME;
begin end;
