package body foo is end;
package body foo is end package body;
package body foo is end package body foo;

package body TriState is
	function BitVal (Value: Tri) return Bit is
		constant Bits : Bit_Vector := "0100";
	begin
		return Bits(Tri'Pos(Value));
	end;

	function TriVal (Value: Bit) return Tri is
	begin
		return Tri'Val(Bit'Pos(Value));
	end;

	function Resolve (Sources: TriVector) return Tri is
		variable V: Tri := 'Z';
	begin
		for i in Sources'Range loop
			if Sources(i) /= 'Z' then
				if V = 'Z' then
					V := Sources(i);
				else
					return 'E';
				end if;
			end if;
		end loop;
		return V;
	end;
end package body TriState;
