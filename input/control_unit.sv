`include "audioport.svh"

import audioport_pkg::*;

module control_unit
  (
   input logic 			       clk,
   input logic 			       rst_n,
   input logic 			       PSEL,
   input logic 			       PENABLE,
   input logic 			       PWRITE,
   input logic [31:0] 		       PADDR,
   input logic [31:0] 		       PWDATA,
   input logic 			       req_in,
   output logic [31:0] 		       PRDATA,
   output logic 		       PSLVERR,
   output logic 		       PREADY,
   output logic 		       irq_out,
   output logic [31:0] 		       cfg_reg_out,
   output logic [31:0] 		       level_reg_out,
   output logic [DSP_REGISTERS*32-1:0] dsp_regs_out,
   output logic 		       cfg_out,
   output logic 		       clr_out,
   output logic 		       level_out,
   output logic 		       tick_out,
   output logic [23:0] 		       audio0_out,
   output logic [23:0] 		       audio1_out,
   output logic 		       play_out
   );


   
endmodule
