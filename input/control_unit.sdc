######################################################################
# control_unit.sdc: Timing Constraints File
######################################################################

# 1. Define clock period and clock edge times in ns

create_clock -name clk -period 10.0 clk

# 2. Define reset input timing wrt clock in ns

set_input_delay  -clock clk 0.0 rst_n

# 3. Define input external delays (arrival times) wrt clock in ns

set_input_delay -clock clk 0.0 PSEL
set_input_delay -clock clk 0.0 PENABLE
set_input_delay -clock clk 0.0 PWRITE
set_input_delay -clock clk 0.0 PADDR
set_input_delay -clock clk 0.0 PWDATA
set_input_delay -clock clk 0.0 req_in

# 4. Define output external delays (setup times) wrt clock in ns

set_output_delay -clock clk 0.0 PRDATA
set_output_delay -clock clk 0.0 PREADY
set_output_delay -clock clk 0.0 PSLVERR
set_output_delay -clock clk 0.0 irq_out
set_output_delay -clock clk 0.0 audio0_out
set_output_delay -clock clk 0.0 audio1_out
set_output_delay -clock clk 0.0 cfg_out
set_output_delay -clock clk 0.0 cfg_reg_out
set_output_delay -clock clk 0.0 level_out
set_output_delay -clock clk 0.0 level_reg_out
set_output_delay -clock clk 0.0 dsp_regs_out
set_output_delay -clock clk 0.0 clr_out   
set_output_delay -clock clk 0.0 tick_out
set_output_delay -clock clk 0.0 play_out

