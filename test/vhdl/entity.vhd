entity Latch is
	port (
		Din: in Word;
		Dout: out Word;
		Load: in Bit;
		Clk: in Bit);
	constant Setup: Time := 12 ns;
	constant PulseWidth: Time := 50 ns;
	use Work.TimingMonitors.all;
begin
	assert Clk='1' or Clk'Delayed'Stable (PulseWidth);
	CheckTiming (Setup, Din, Load, Clk);
end;
