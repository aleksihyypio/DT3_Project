-------------------------------------------------------------------------------
-- i2s_unit.vhd:  VHDL RTL model for the i2s_unit.
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

-------------------------------------------------------------------------------
-- Entity declaration
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

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

begin

      
  
end RTL;

