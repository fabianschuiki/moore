library ieee;
use ieee.std_logic_1164.all;

package pkg_bit_string_literals is
	constant b000 : std_logic_vector(7 downto 0) := B"00000000";
	constant b001 : std_logic_vector(7 downto 0) := B"01010011";
	constant b002 : std_logic_vector(7 downto 0) :=  "00000000";
	constant b003 : std_logic_vector(7 downto 0) :=  "01010011";

	constant x000 : std_logic_vector(7 downto 0) := x"00";
	constant x001 : std_logic_vector(7 downto 0) := x"AB";
	constant x002 : std_logic_vector(7 downto 0) := x"ab";
	constant x003 : std_logic_vector(7 downto 0) := x"aB";
	constant x004 : std_logic_vector(7 downto 0) := X"00";
	constant x005 : std_logic_vector(7 downto 0) := X"AB";
	constant x006 : std_logic_vector(7 downto 0) := X"ab";
	constant x007 : std_logic_vector(7 downto 0) := X"aB";

	constant o000 : std_logic_vector(5 downto 0) := O"00";
	constant o001 : std_logic_vector(5 downto 0) := O"11";
	constant o002 : std_logic_vector(5 downto 0) := O"13";
	constant o003 : std_logic_vector(5 downto 0) := O"07";

  -- the cases below are actually not accepted by some commercial tools
  -- I still think they are correct according to the standard
	constant u000 : std_logic_vector(7 downto 0) := x"0_0";
	constant u001 : std_logic_vector(7 downto 0) := "0000_0000";
	constant u002 : std_logic_vector(7 downto 0) := "0_00_0_00_00";

	constant ux000 : std_logic_vector(7 downto 0) := Ux"AB";
	constant ux001 : std_logic_vector(7 downto 0) := Ux"AB";
	constant ux002 : std_logic_vector(7 downto 0) := UX"AB";
	constant ux003 : std_logic_vector(7 downto 0) := uX"AB";
	constant ux004 : std_logic_vector(7 downto 0) := 8ux"00000AB";

	constant sx000 : std_logic_vector(7 downto 0) := Sx"AB";
	constant sx001 : std_logic_vector(7 downto 0) := Sx"AB";
	constant sx002 : std_logic_vector(7 downto 0) := SX"AB";
	constant sx003 : std_logic_vector(7 downto 0) := sX"AB";
	constant sx004 : std_logic_vector(7 downto 0) := 8sx"FFFFFAB";
	constant sx005 : std_logic_vector(7 downto 0) := 8sx"FFAB";
	constant sx006 : std_logic_vector(7 downto 0) := 8sx"00000AB";
	constant sx007 : std_logic_vector(7 downto 0) := 8sx"00AB";

	constant d000 : std_logic_vector(7 downto 0) := 8D"0";
	constant d001 : std_logic_vector(7 downto 0) := 8D"255";
	constant d002 : std_logic_vector(7 downto 0) := 8D"128";
	constant d003 : std_logic_vector(7 downto 0) := 8D"12";
	constant d003 : std_logic_vector(7 downto 0) := 8D"12";

	constant x007 : std_logic_vector(7 downto 0) := 8X"aB";
end package;
