////////////////////////////////////////////////////////////////////////////////////////////
//
// SystemVerilog assertion module file for control_unit
//
//    Contents:
//    1. X-Checks
//    2. Blackbox (functional) assumptions and assertions
//    3. Whitebox assertions
//    4. Covergroups
//
////////////////////////////////////////////////////////////////////////////////////////////

`include "audioport.svh"

import audioport_pkg::*;
import audioport_util_pkg::*;

module control_unit_svamod
  (
   input logic 					   clk,
   input logic 					   rst_n,
   input logic 					   PSEL,
   input logic 					   PENABLE,
   input logic 					   PWRITE,
   input logic [31:0] 				   PADDR,
   input logic [31:0] 				   PWDATA,
   input logic 					   req_in,
   input logic [31:0] 				   PRDATA,
   input logic 					   PSLVERR,
   input logic 					   PREADY,
   input logic 					   irq_out,
   input logic [31:0] 				   cfg_reg_out,
   input logic [31:0] 				   level_reg_out,
   input logic [DSP_REGISTERS*32-1:0] 		   dsp_regs_out,
   input logic 					   cfg_out,
   input logic 					   clr_out,
   input logic 					   level_out,
   input logic 					   tick_out,
   input logic [23:0] 				   audio0_out,
   input logic [23:0] 				   audio1_out,
   input logic 					   play_out
`ifndef SYSTEMC_DUT						   ,
   input logic [$clog2(AUDIOPORT_REGISTERS+2)-1:0] rindex,
   input logic 					   apbwrite,
   input logic 					   apbread,
   input logic [AUDIOPORT_REGISTERS-1:0][31:0] 	   rbank_r,
   input logic 					   start,
   input logic 					   stop,
   input logic 					   clr,
   input logic 					   irqack,
   input logic 					   req_r,
   input logic 					   play_r,
   input logic 					   irq_r,
   input logic [AUDIO_FIFO_SIZE-1:0][23:0] 	   ldata_r,
   input logic [$clog2(AUDIO_FIFO_SIZE)-1:0] 	   lhead_r,
   input logic [$clog2(AUDIO_FIFO_SIZE)-1:0] 	   ltail_r, 
   input logic 					   llooped_r,
   input logic 					   lempty,
   input logic 					   lfull,
   input logic [23:0] 				   lfifo,
   input logic [AUDIO_FIFO_SIZE-1:0][23:0] 	   rdata_r,
   input logic [$clog2(AUDIO_FIFO_SIZE)-1:0] 	   rhead_r,
   input logic [$clog2(AUDIO_FIFO_SIZE)-1:0] 	   rtail_r, 
   input logic 					   rlooped_r,
   input logic 					   rempty,
   input logic 					   rfull,
   input logic [23:0] 				   rfifo 
  
`endif

   );


   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 1. X-checks
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

   `xcheck(PSEL);
   `xcheck(PENABLE);
   `xcheck(PWRITE);
   `xcheck(PADDR);
   `xcheck(PWDATA);
   `xcheck(req_in);
   `xcheck(PRDATA);
   `xcheck(PSLVERR);
   `xcheck(PREADY);
   `xcheck(irq_out);
   `xcheck(cfg_reg_out);
   `xcheck(level_reg_out);
   `xcheck(dsp_regs_out);
   `xcheck(cfg_out);
   `xcheck(clr_out);
   `xcheck(level_out);
   `xcheck(tick_out);
   `xcheck(audio0_out);
   `xcheck(audio1_out);
   `xcheck(play_out);
`ifndef SYSTEMC_DUT
   `xcheck(rindex);
   `xcheck(apbwrite);
   `xcheck(apbread);
   `xcheck(rbank_r);
   `xcheck(start);
   `xcheck(stop);
   `xcheck(clr);
   `xcheck(irqack);
   `xcheck(req_r);
   `xcheck(play_r);
   `xcheck(irq_r);
   `xcheck(ldata_r);
   `xcheck(lhead_r);
   `xcheck(ltail_r); 
   `xcheck(llooped_r);
   `xcheck(lempty);
   `xcheck(lfull);
   `xcheck(lfifo);
   `xcheck(rdata_r);
   `xcheck(rhead_r);
   `xcheck(rtail_r); 
   `xcheck(rlooped_r);
   `xcheck(rempty);
   `xcheck(rfull);
   `xcheck(rfifo);
`endif

   
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 2. Blackbox (functional) assumptions and assertions
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

   
   // Assumptions for APB ports
   
`include "apb_assumes.svh"

   // Assumption for req_in port

   // req_in_pulse : f_req_in_pulse
   property f_req_in_pulse;
   @(posedge clk ) disable iff (rst_n == '0)
     $rose(req_in) |=> $fell(req_in);
endproperty

   mf_req_in_pulse: assume property(f_req_in_pulse) else assert_error("mf_req_in_pulse");



   // Black box (functional assertions)
   

   // req_in_first : f_req_in_first

   property f_req_in_first;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   mf_req_in_first: assume property(f_req_in_first) else assert_error("mf_req_in_first");


   // apb_ports : f_pready_on

   property f_pready_on;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_pready_on: assert property(f_pready_on) else assert_error("af_pready_on");
   cf_pready_on: cover property(f_pready_on);

   // apb_ports : f_pslverr_off

   property f_pslverr_off;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_pslverr_off: assert property(f_pslverr_off) else assert_error("af_pslverr_off");
   cf_pslverr_off: cover property(f_pslverr_off);

   // prdata_driving : f_prdata_off

   property f_prdata_off;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_prdata_off: assert property(f_prdata_off) else assert_error("af_prdata_off");
   cf_prdata_off: cover property(f_prdata_off);

   // cmd_clr, command_interface : f_clr_out_pulse

   property f_clr_out_pulse;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_clr_out_pulse: assert property(f_clr_out_pulse) else assert_error("af_clr_out_pulse");
   cf_clr_out_pulse: cover property(f_clr_out_pulse);

   // cmd_clr, command_interface, : f_clr_out_valid_high

   property f_clr_out_valid_high;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_clr_out_valid_high: assert property(f_clr_out_valid_high) else assert_error("af_clr_out_valid_high");
   cf_clr_out_valid_high: cover property(f_clr_out_valid_high);

   // cmd_cfg, command_interface : f_cfg_out_pulse

   property f_cfg_out_pulse;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_cfg_out_pulse: assert property(f_cfg_out_pulse) else assert_error("af_cfg_out_pulse");
   cf_cfg_out_pulse: cover property(f_cfg_out_pulse);

   // cmd_cfg, command_interface : f_cfg_out_valid_high

   property f_cfg_out_valid_high;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_cfg_out_valid_high: assert property(f_cfg_out_valid_high) else assert_error("af_cfg_out_valid_high");
   cf_cfg_out_valid_high: cover property(f_cfg_out_valid_high);

   // modes, cmd_start, command_interface : f_start_play

   property f_start_play;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_start_play: assert property(f_start_play) else assert_error("af_start_play");
   cf_start_play: cover property(f_start_play);

   // cmd_start, command_interface : f_valid_start_play

   property f_valid_start_play;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_valid_start_play: assert property(f_valid_start_play) else assert_error("af_valid_start_play");
   cf_valid_start_play: cover property(f_valid_start_play);

   // modes, cmd_stop, command_interface : f_stop_play

   property f_stop_play;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_stop_play: assert property(f_stop_play) else assert_error("af_stop_play");
   cf_stop_play: cover property(f_stop_play);

   // cmd_stop, command_interface : f_valid_stop_play

   property f_valid_stop_play;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_valid_stop_play: assert property(f_valid_stop_play) else assert_error("af_valid_stop_play");
   cf_valid_stop_play: cover property(f_valid_stop_play);

   // cmd_level, command_interface : f_level_out_pulse

   property f_level_out_pulse;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_level_out_pulse: assert property(f_level_out_pulse) else assert_error("af_level_out_pulse");
   cf_level_out_pulse: cover property(f_level_out_pulse);

   // cmd_level, command_interface : f_level_out_valid_high

   property f_level_out_valid_high;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_level_out_valid_high: assert property(f_level_out_valid_high) else assert_error("af_level_out_valid_high");
   cf_level_out_valid_high: cover property(f_level_out_valid_high);

   // req_tick_logic : f_tick_standby

   property f_tick_standby;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_tick_standby: assert property(f_tick_standby) else assert_error("af_tick_standby");
   cf_tick_standby: cover property(f_tick_standby);

   // req_tick_logic : f_tick_out_high

   property f_tick_out_high;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_tick_out_high: assert property(f_tick_out_high) else assert_error("af_tick_out_high");
   cf_tick_out_high: cover property(f_tick_out_high);

   // req_tick_logic : f_tick_out_low

   property f_tick_out_low;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_tick_out_low: assert property(f_tick_out_low) else assert_error("af_tick_out_low");
   cf_tick_out_low: cover property(f_tick_out_low);

`ifndef RTL_VERIF
   
   // fifo_reading : f_fifo_drain

   property f_fifo_drain;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_fifo_drain: assert property(f_fifo_drain) else assert_error("af_fifo_drain");
   cf_fifo_drain: cover property(f_fifo_drain);

   // irq_up : f_irq_out_rise_first

   property f_irq_out_rise_first;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_irq_out_rise_first: assert property(f_irq_out_rise_first) else assert_error("af_irq_out_rise_first");
   cf_irq_out_rise_first: cover property(f_irq_out_rise_first);

`endif //  `ifndef RTL_VERIF
   
   // irq_up : f_irq_out_high

   property f_irq_out_high;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_irq_out_high: assert property(f_irq_out_high) else assert_error("af_irq_out_high");
   cf_irq_out_high: cover property(f_irq_out_high);

   // modes : f_irq_out_standby

   property f_irq_out_standby;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_irq_out_standby: assert property(f_irq_out_standby) else assert_error("af_irq_out_standby");
   cf_irq_out_standby: cover property(f_irq_out_standby);

   // irq_down, cmd_irqack, command_interface : f_irq_out_down

   property f_irq_out_down;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_irq_out_down: assert property(f_irq_out_down) else assert_error("af_irq_out_down");
   cf_irq_out_down: cover property(f_irq_out_down);

   // cfg_reg_out_driving : f_cfg_reg_drv

   property f_cfg_reg_drv;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_cfg_reg_drv: assert property(f_cfg_reg_drv) else assert_error("af_cfg_reg_drv");
   cf_cfg_reg_drv: cover property(f_cfg_reg_drv);

   // level_reg_out_driving : f_level_reg_drv

   property f_level_reg_drv;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_level_reg_drv: assert property(f_level_reg_drv) else assert_error("af_level_reg_drv");
   cf_level_reg_drv: cover property(f_level_reg_drv);

   // dsp_regs_out_conn : f_dsp_regs_drv

   property f_dsp_regs_drv;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_dsp_regs_drv: assert property(f_dsp_regs_drv) else assert_error("af_dsp_regs_drv");
   cf_dsp_regs_drv: cover property(f_dsp_regs_drv);


   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 3. Whitebox (RTL) assertions
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

`ifndef SYSTEMC_DUT

 `include "control_unit_wba.svh"

`endif //  `ifndef SYSTEMC_DUT
   
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 4. Covergroups
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

`ifndef SYSTEMC_DUT


   
`endif //  `ifndef SYSTEMC_DUT

endmodule

