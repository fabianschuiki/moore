package pkg is
	type TWOS_COMPLEMENT_INTEGER is range -32768 to 32767;
	type BYTE_LENGTH_INTEGER is range 0 to 255;
	type WORD_INDEX is range 31 downto 0;
	--subtype HIGH_BIT_LOW is BYTE_LENGTH_INTEGER range 0 to 127;
end;

library work;
entity foo is
	port (
		A: in work.pkg.TWOS_COMPLEMENT_INTEGER;
		B: in work.pkg.BYTE_LENGTH_INTEGER;
		C: in work.pkg.WORD_INDEX
		--D: in work.pkg.HIGH_BIT_LOW
	);
end;
architecture bar of foo is begin end;
