entity reg is
	generic(
	width: integer:=32
);
port(
clk: in bit;
regdata_i: in bit_vector(width-1 downto 0);
regdata_o: out bit_vector(width-1 downto 0)
);
end entity;

architecture rtl of reg is
	signal reg: bit_vector(width-1 downto 0);
begin
	process(clk)
	begin
		if(clk'event and clk='1') then
			reg<=regdata_i;
		end if;
	end process;
	regdata_o<=reg;
end rtl;

entity testreg is
	end entity;

architecture rtl of testreg is
	component reg is
		generic(
		width: integer:=32
	);
	port(
	clk: in bit;
	regdata_i: in bit_vector(width-1 downto 0);
	regdata_o: out bit_vector(width-1 downto 0)
);
	end component;
	signal clk:bit;
begin

genclk: process begin 
	clk <= '1';
	wait for 1 us;
	clk <= '0';
	wait for 1 us;
end process;

r1:reg
generic map(width=>8)
port map(clk=>clk,regdata_i=>x"ff");
end architecture;
