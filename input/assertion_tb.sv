// assertion_tb.sv: Simple testbench for debugging assertions 
//
// Usage:
//      1. Create a scenario where an assertion a_X based on property X should
//         PASS and FAIL in the initial proceudre below
//      2. Run the script to verify that the waveforms look OK
//         vsim -do scripts/assertion_tb.tcl
//      3. Declare the property and assertions below the initial process
//      4. Run the script again. The script puts all assertions in the Wave window.
//         Expand an assertion (+) and its ActiveCount (+) to view evaluation details
//      5. To get a detailed view of assertion evaluation, do the following:
//         a) Activate the Assertions tab
//         b) Select an assertion
//         c) Using the right button, execure View ATV.. and select a specific
//            passing or failure of the assertion (ATV = assertion thread view)
//         d) You can now follow the evaluation of property expressions in time
// 

import audioport_pkg::*;

module assertion_tb; 
   
   // Clock and reset 
   logic clk = '0, rst_n = 0; 
   always #10ns clk = ~clk; 
   initial @(negedge clk) rst_n = '1; 

   logic        PSEL;
   logic        PENABLE;
   logic        PWRITE;
   logic [31:0] PADDR;
   logic [31:0] PWDATA;
   logic 	PREADY;
   logic [23:0] audio0_out;
   logic [23:0] audio1_out;
   logic	tick_out;
   
   ///////////////////////////////////////////////////////////////////
   // Test data generation process for DSP registers
   ///////////////////////////////////////////////////////////////////
   
   initial begin
    // Case 1: Proper FIFO drain
     tick_out = 1;
     @(negedge clk);
     tick_out = 0;
     audio0_out = 0;
     audio1_out = 0;
     @(negedge clk);
     // Case 2: Improper FIFO drain (should fail)
     tick_out = 1;
     @(negedge clk);
     audio0_out = $random;
     audio1_out = $random;
     @(negedge clk);
     // End simulation
     $finish;
   end

   ///////////////////////////////////////////////////////////////////
   // Generate block for assertions
   ///////////////////////////////////////////////////////////////////
   
   // fifo_reading : f_fifo_drain

   property f_fifo_drain;
     @(posedge clk) disable iff (rst_n == '0)
       $rose(tick_out) |-> ##[1:$] 
       (!(PSEL && PENABLE && PWRITE && ((PADDR == LEFT_FIFO_ADDRESS) || (PADDR == RIGHT_FIFO_ADDRESS)))) ##[1:AUDIO_FIFO_SIZE] 
       (audio0_out == '0 && audio1_out == '0);
   endproperty


endmodule 
