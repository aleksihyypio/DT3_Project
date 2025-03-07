-------------------------------------------------------------------------------
-- i2s_unit.vhd:  VHDL RTL model for the i2s_unit.
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

-------------------------------------------------------------------------------
-- Entity declaration
-------------------------------------------------------------------------------

entity i2s_unit is
  
  port (
    clk   : in std_logic;
    rst_n : in std_logic;
    play_in : in std_logic;
    tick_in : in std_logic;
    audio0_in : in std_logic_vector(23 downto 0);
    audio1_in : in std_logic_vector(23 downto 0);    
    req_out : out std_logic;
    ws_out : out std_logic;
    sck_out : out std_logic;
    sdo_out : out std_logic
  );
  
end i2s_unit;

-------------------------------------------------------------------------------
-- Architecture declaration
-------------------------------------------------------------------------------

architecture RTL of i2s_unit is

   signal mode_reg         : std_logic;				-- 0 = Standby, 1 = Play mode
   signal audio_data_reg   : std_logic_vector(47 downto 0);
   signal shift_reg        : std_logic_vector(47 downto 0);
   signal counter_reg      : unsigned(8 downto 0);
   signal next_mode_logic  : std_logic;
   signal audio_data_logic : std_logic;
   signal shift_logic      : std_logic;
   signal counter_logic    : std_logic;
   signal req_out_logic	   : std_logic;

begin
   -- Output assignments
   req_out <= req_out_logic;
   sck_out <= '1' when (mode_reg = '1' and counter_reg(2 downto 0) < "100") else '0';
   ws_out  <= '1' when (mode_reg = '1' and counter_reg >= 188 and counter_reg <= 379) else '0';
   sdo_out <= shift_reg(47);
   -- Logic for outputs
   req_out_logic <= '1' when (mode_reg = '1' and play_in = '1' and counter_reg = 3) else '0';
   -- Logic for internal signals
   next_mode_logic <= '1' when (mode_reg = '0' and play_in = '1') else 
   '0' when (mode_reg = '1' and play_in = '0' and counter_reg = 7
   and shift_reg = "000000000000000000000000000000000000000000000000") else
   mode_reg;
   audio_data_logic <= '1' when (tick_in = '1' and play_in = '1' and counter_reg = 4) else '0';
   shift_logic <= '1' when (mode_reg = '1' and counter_reg > 3 
   and counter_reg(2 downto 0) = "011") else
   '1' when (mode_reg = '1' and play_in = '0' and counter_reg = 3) else '0';
   counter_logic <= '1' when (mode_reg = '1' and counter_reg = 383) else '0';
   -- Sequential logic
   process (clk, rst_n)
   begin
     if rst_n = '0' then
       mode_reg <= '0';
       audio_data_reg <= (others => '0');
       shift_reg <= (others => '0');
       counter_reg <= (others => '0');
     elsif rising_edge(clk) then
       mode_reg <= next_mode_logic;
       if mode_reg = '0' then
         audio_data_reg <= (others => '0');
         shift_reg <= (others => '0');
	 counter_reg <= (others => '0');
       else
       if audio_data_logic = '1' then
         audio_data_reg <= audio0_in & audio1_in; 
       end if;
       if req_out_logic = '1' then
	 shift_reg <= audio_data_reg;
       elsif shift_logic = '1' then
         shift_reg <= shift_reg(46 downto 0) & '0';
       end if;    
       if counter_logic = '1' then
        counter_reg <= (others => '0');
       else
        counter_reg <= counter_reg + 1;
       end if;
     end if;
   end if;
   end process;
end RTL;

