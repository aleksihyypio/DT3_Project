////////////////////////////////////////////////////////////////////////////////////////////
//
// SystemVerilog assertion module file for i2s_unit
//
//    Contents:
//    1. X-Checks
//    2. Assumptions fro formal verification
//    3. Blackbox assertions
//    4. Whitebox assertions
//    5. Covergroups
//
////////////////////////////////////////////////////////////////////////////////////////////

`include "audioport.svh"

import audioport_pkg::*;
import audioport_util_pkg::*;

module i2s_unit_svamod
  (
   input logic 	      clk,
   input logic 	      rst_n,
   input logic 	      play_in,
   input logic [23:0] audio0_in,
   input logic [23:0] audio1_in,
   input logic 	      tick_in,
   input logic 	      req_out,
   input logic 	      sck_out,
   input logic 	      ws_out,
   input logic 	      sdo_out
`ifndef SYSTEMC_DUT		,
   // To add ports for internal signals of DUT, uncomment the comma on the next line 
   // and add the signal names
   input logic		mode_reg,
   input logic [47:0]	audio_data_reg,
   input logic [47:0]	shift_reg,
   input logic [8:0]	counter_reg,
   input logic		next_mode_logic,
   input logic		audio_data_logic,
   input logic		req_out_logic,
   input logic		sck_out_logic,
   input logic		ws_out_logic,
   input logic		shift_logic,
   input logic		counter_logic
`endif
   );

   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 1. X-checks
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

   `xcheck(play_in);
   `xcheck(audio0_in);
   `xcheck(audio1_in);
   `xcheck(tick_in);
   `xcheck(req_out);
   `xcheck(sck_out);
   `xcheck(ws_out);
   `xcheck(sdo_out);
`ifndef SYSTEMC_DUT
   `xcheck(mode_reg);
   `xcheck(audio_data_reg);
   `xcheck(shift_reg);
   `xcheck(counter_reg);
   `xcheck(next_mode_logic);
   `xcheck(audio_data_logic);
   `xcheck(req_out_logic);
   `xcheck(sck_out_logic);
   `xcheck(ws_out_logic);
   `xcheck(shift_logic);
   `xcheck(counter_logic);
`endif   
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 2. Blackbox (functional) assumptions and assertions
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

`ifdef design_top_is_i2s_unit // Assumptions enabled only in i2s_unit verification

   // play_in_length : f_play_in_stable

   property f_play_in_stable;
   @(posedge clk ) disable iff (rst_n == '0)
     !$stable(play_in) |=> $stable(play_in) [* 384];
   endproperty

   mf_play_in_stable: assume property(f_play_in_stable) else assert_error("mf_play_in_stable");
   cf_play_in_stable: cover property(f_play_in_stable);

   // tick_in_length : f_tick_in_pulse

   property f_tick_in_pulse;
      @(posedge clk ) disable iff (rst_n == '0)
	$rose(tick_in) |=> $fell(tick_in);
   endproperty

   mf_tick_in_pulse: assume property(f_tick_in_pulse) else assert_error("mf_tick_in_pulse");
   cf_tick_in_pulse: cover property(f_tick_in_pulse);

   // tick_in_length : f_tick_in_play_only

   property f_tick_in_play_only;
      @(posedge clk ) disable iff (rst_n == '0)
	!play_in |-> !tick_in;
   endproperty

   mf_tick_in_play_only: assume property(f_tick_in_play_only) else assert_error("mf_tick_in_play_only");
   cf_tick_in_play_only: cover property(f_tick_in_play_only);

`endif //  `ifdef design_top_is_i2s_unit


   
   // data_request : f_req_out_pulse

   property f_req_out_pulse;
      @(posedge clk ) disable iff (rst_n == '0)
	$rose(req_out) |=> $fell(req_out);
   endproperty

   af_req_out_pulse: assert property(f_req_out_pulse) else assert_error("af_req_out_pulse");
   cf_req_out_pulse: cover property(f_req_out_pulse);


   
   // mode_control : f_sck_start
   
   property f_sck_start;
      @(posedge clk ) disable iff (rst_n == '0)
	$rose(play_in)  |=> $rose(sck_out);
   endproperty
   
   af_sck_start: assert property(f_sck_start) else assert_error("af_sck_start");
   cf_sck_start: cover property(f_sck_start);
   
   // data_request : f_req_sck_align

   property f_req_sck_align;
      @(posedge clk ) disable iff (rst_n == '0)
	$fell(req_out) |-> $fell(sck_out);
   endproperty

   af_req_sck_align: assert property(f_req_sck_align) else assert_error("af_req_sck_align");
   cf_req_sck_align: cover property(f_req_sck_align);

   // data_request : f_req_out_seen

   property f_req_out_seen;
      @(posedge clk ) disable iff (rst_n == '0)
	($rose(play_in) || (play_in && $fell(ws_out))) ##1 (play_in throughout ($fell(sck_out) [-> 1])) |-> $past(req_out);
   endproperty

   af_req_out_seen: assert property(f_req_out_seen) else assert_error("af_req_out_seen");
   cf_req_out_seen: cover property(f_req_out_seen);

   // sck_wave : f_sck_wave

   property f_sck_wave;
      @(posedge clk ) disable iff (rst_n == '0)
	$rose(sck_out) |=> (sck_out [*3] ##1 !sck_out[*4]) or
					  (sck_out [*1] ##1 !sck_out[*2]) or 
					  $fell(sck_out);
   endproperty

   af_sck_wave: assert property(f_sck_wave) else assert_error("af_sck_wave");
   cf_sck_wave: cover property(f_sck_wave);

   // ws_wave : f_ws_change

   property f_ws_change;
      @(posedge clk ) disable iff (rst_n == '0)
	!$stable(ws_out) |-> $fell(sck_out);
   endproperty

   af_ws_change: assert property(f_ws_change) else assert_error("af_ws_change");
   cf_ws_change: cover property(f_ws_change);

   // ws_wave : f_ws_wave

   property f_ws_wave;
      @(posedge clk ) disable iff (rst_n == '0)
	!ws_out throughout $rose(sck_out) [-> 24] |=> $rose(ws_out) [-> 1] ##1 (ws_out throughout $rose(sck_out) [-> 24]) ;
   endproperty

   af_ws_wave: assert property(f_ws_wave) else assert_error("af_ws_wave");
   cf_ws_wave: cover property(f_ws_wave);

   // serial_data : f_sdo_change

   property f_sdo_change;
      @(posedge clk ) disable iff (rst_n == '0)
	!$stable(sdo_out) && play_in |-> $fell(sck_out);
   endproperty

   af_sdo_change: assert property(f_sdo_change) else assert_error("af_sdo_change");
   cf_sdo_change: cover property(f_sdo_change);




   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 3. Whitebox (RTL) assertions
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

 `ifndef SYSTEMC_DUT

   // mode_control : r_mode_transition

   property r_mode_transition;
	@(posedge clk) disable iff (!rst_n)
	  ($rose(play_in)) |=> (mode_reg == 1) ##1 (sck_out || req_out);
   endproperty

   ar_mode_transition: assert property(r_mode_transition) else assert_error("ar_mode_transition");
   cr_mode_transition: cover property(r_mode_transition);

   // mode_control : r_mode_standby_outputs

   property r_mode_standby_outputs;
	@(posedge clk) disable iff (!rst_n)
	  (mode_reg == 0) |=> (sck_out == 0 && ws_out == 0 && sdo_out == 0);
   endproperty

   ar_mode_standby_outputs: assert property(r_mode_standby_outputs) else assert_error("ar_modes_standby_outputs");
   cr_mode_standby_outputs: cover property(r_mode_standby_outputs);

   // mode_control : r_mode_play_delay

   property r_mode_play_delay;
	@(posedge clk) disable iff (!rst_n)
	   ($rose(play_in)) |=> ($rose(sck_out)) [*1];
   endproperty

   ar_mode_play_delay: assert property(r_mode_play_delay) else assert_error("ar_mode_play_delay");
   cr_mode_play_delay: cover property(r_mode_play_delay);

   // audio_interface : r_audio_data_load_enable

   property r_audio_data_load_enable;
	@(posedge clk) disable iff (!rst_n)
	   (tick_in && play_in) |=> (audio_data_reg == {audio0_in, audio1_in});
   endproperty

   ar_audio_data_load_enable: assert property(r_audio_data_load_enable) else assert_error("ar_audio_data_load_enable");
   cr_audio_data_load_enable: cover property(r_audio_data_load_enable);

   // audio_interface : r_audio_data_zero

   property r_audio_data_zero;
	@(posedge clk) disable iff(!rst_n)
	   (mode_reg == 0) |=> (audio_data_reg == '0);
   endproperty

   ar_audio_data_zero: assert property(r_audio_data_zero) else assert_error("ar_audio_data_zero");
   cr_audio_data_zero: cover property(r_audio_data_zero);

   // shift_register : r_shift_reg_load

   property r_shift_reg_load;
	@(posedge clk) disable iff(!rst_n)
	  ($rose(req_out)) |=> (shift_reg == audio_data_reg);
   endproperty

   ar_shift_reg_load: assert property(r_shift_reg_load) else assert_error("ar_shift_reg_load");
   cr_shift_reg_load: cover property(r_shift_reg_load);

   // shift_register : r_first_sample_zero

   property r_first_sample_zero;
	@(posedge clk) disable iff(!rst_n)
	   ($rose(play_in)) |=> (shift_reg == '0);
   endproperty

   ar_first_sample_zero: assert property(r_first_sample_zero) else assert_error("ar_first_sample_zero");
   cr_first_sample_zero: cover property(r_first_sample_zero);

   // shift_register : r_shift_reg_zero

   property r_shift_reg_zero;
	@(posedge clk) disable iff(!rst_n)
	   (mode_reg == 0) |=> (shift_reg == '0);
   endproperty

   ar_shift_reg_zero: assert property(r_shift_reg_zero) else assert_error("ar_shift_reg_zero");
   cr_shift_reg_zero: cover property(r_shift_reg_zero);

   // sck_/ws_wave : r_counter_reg_reset

   property r_counter_reg_reset;
	@(posedge clk) disable iff(!rst_n)
	   (counter_reg == 9'b101111111) |=> (counter_reg == '0);
   endproperty

   ar_counter_reg_reset: assert property(r_counter_reg_reset) else assert_error("ar_counter_reg_reset");
   cr_counter_reg_reset: cover property(r_counter_reg_reset);

   // data_request : f_req_out_first_frame

   property f_req_out_first_frame;
	@(posedge clk) disable iff(!rst_n)
	   ($rose(play_in)) |=> ($rose(req_out));
   endproperty

   af_req_out_first_frame: assert property(f_req_out_first_frame) else assert_error("af_req_out_first_frame");
   cf_req_out_first_frame: cover property(f_req_out_first_frame);

   // serial_data : f_sdo_out_conn

   property f_sdo_out_conn;
	@(posedge clk) disable iff(!rst_n)
	   (sdo_out == shift_reg[47]);
   endproperty

   af_sdo_out_conn: assert property(f_sdo_out_conn) else assert_error("af_sdo_out_conn");
   cf_sdo_out_conn: cover property(f_sdo_out_conn);

   // serial_data : r_shift_operation_timing
   
   property r_shift_operation_timing;
	@(posedge clk) disable iff(!rst_n)
	   ($fell(sck_out) && !req_out) |=> (shift_reg == shift_reg << 1);
   endproperty

   ar_shift_operation_timing: assert property(r_shift_operation_timing) else assert_error("r_shift_operation_timing");
   cr_shift_operation_timing: cover property(r_shift_operation_timing);

 `endif

   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 4. Covergroups
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////



endmodule

