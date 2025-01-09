`include "audioport.svh"

import audioport_pkg::*;

module cdc_unit
  (
   input logic 	       clk,
   input logic 	       rst_n,
   input logic 	       test_mode_in,
   input logic [23:0]  audio0_in,
   input logic [23:0]  audio1_in,
   input logic 	       play_in,
   input logic 	       tick_in,
   output logic        req_out,

   input logic 	       mclk,
   output logic        muxclk_out,
   output logic        muxrst_n_out,
   output logic [23:0] audio0_out,
   output logic [23:0] audio1_out, 
   output logic        play_out,
   output logic        tick_out,
   input logic 	       req_in		
   );
   
   logic 	       mrst_n;
   logic 	       muxrst_n;
   logic 	       muxclk;
   logic 	       rsync_clk;
   
   
endmodule





