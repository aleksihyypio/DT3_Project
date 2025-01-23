//////////////////////////////////////////////////////////////////////////////////////
task reset_test;
//////////////////////////////////////////////////////////////////////////////////////   
   @(negedge clk);   
   req_in = '0;
   apb.init;
   rst_n = '1;   
   @(negedge clk);   
   rst_n = '0;
   @(negedge clk);
   @(negedge clk);   
   rst_n = '1;
endtask

//////////////////////////////////////////////////////////////////////////////////////
task apb_test;
//////////////////////////////////////////////////////////////////////////////////////
   
 // Print a message to user   
   $info("apb_test");

   // 1.
   reset_test;
   req_in = '0;
   
   // 2
   addr = CMD_REG_ADDRESS;
   wdata = CMD_NOP;
   apb.write(addr, wdata, wfail);
   apb.read(addr, rdata, rfail);   
   ia_apb_test1: assert (!wfail && !rfail) else 
     assert_error("ia_apb_test1");  // See assert_error in audioport_pkg.sv

   //3 
   repeat(10)
     @(posedge clk);
   
   // 4
   addr = AUDIOPORT_START_ADDRESS-4;
   wdata = $urandom;
   apb.write(addr, wdata, wfail);
   apb.read(addr, rdata, rfail);   

   update_test_stats; // See audioport_pkg.sv
    
endtask

//////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////
task address_decoding_test;
//////////////////////////////////////////////////////////////////////////////////////   
   $info("address_decoding_test");

   reset_test;
   req_in = '0;
   
   // Test valid addresses within range
   for (int addr = AUDIOPORT_START_ADDRESS; addr <= AUDIOPORT_END_ADDRESS; addr += 4) begin
      wdata = addr >> 2; // Example: write expected index
      apb.write(addr, wdata, wfail);
      apb.read(addr, rdata, rfail);
      ia_address_decoding_test1: assert (!wfail && !rfail && (rdata == (addr - AUDIOPORT_START_ADDRESS) >> 2)) else
        assert_error($sformatf ("Address decoding failed for address %h", addr));
   end

   // Test invalid address outside range
   addr = AUDIOPORT_START_ADDRESS - 4;
   apb.write(addr, wdata, wfail);
   apb.read(addr, rdata, rfail);
   ia_address_decoding_test2: assert (wfail && rfail) else 
     assert_error($sformatf ("Invalid address decoding did not fail for address %h", addr));
   
   update_test_stats;

endtask

//////////////////////////////////////////////////////////////////////////////////////
task register_test;
//////////////////////////////////////////////////////////////////////////////////////
   $info("register_test");

   
endtask


//////////////////////////////////////////////////////////////////////////////////////
task fifo_bus_test;
//////////////////////////////////////////////////////////////////////////////////////
   $info("fifo_bus_test");
   
endtask

//////////////////////////////////////////////////////////////////////////////////////
task prdata_off_test;
//////////////////////////////////////////////////////////////////////////////////////
   $info("prdata_off_test");
   
endtask

//////////////////////////////////////////////////////////////////////////////////////
task cmd_start_stop_test;
//////////////////////////////////////////////////////////////////////////////////////   
   $info("cmd_start_stop_test");

endtask

//////////////////////////////////////////////////////////////////////////////////////
task status_test;
//////////////////////////////////////////////////////////////////////////////////////   
   $info("status_test");

endtask

//////////////////////////////////////////////////////////////////////////////////////   
task cmd_clr_test;
//////////////////////////////////////////////////////////////////////////////////////      
   $info("cmd_clr_test");

endtask


//////////////////////////////////////////////////////////////////////////////////////
task cmd_cfg_test;
//////////////////////////////////////////////////////////////////////////////////////   
   $info("cmd_cfg_test");

endtask


//////////////////////////////////////////////////////////////////////////////////////
task cmd_level_test;
//////////////////////////////////////////////////////////////////////////////////////   
   $info("cmd_level_test");

endtask


//////////////////////////////////////////////////////////////////////////////////////
task clr_error_test;
//////////////////////////////////////////////////////////////////////////////////////   
   $info("clr_error_test");

endtask

//////////////////////////////////////////////////////////////////////////////////////
task req_tick_test;
//////////////////////////////////////////////////////////////////////////////////////   
   $info("req_tick_test");

endtask


//////////////////////////////////////////////////////////////////////////////////////
task fifo_test;
//////////////////////////////////////////////////////////////////////////////////////   
   $info("fifo_test");   
endtask

//////////////////////////////////////////////////////////////////////////////////////
task irq_up_test;
//////////////////////////////////////////////////////////////////////////////////////   
   $info("irq_up_test");      

endtask

//////////////////////////////////////////////////////////////////////////////////////
task irq_down_test;
//////////////////////////////////////////////////////////////////////////////////////   
   $info("irq_down_test");
endtask


//////////////////////////////////////////////////////////////////////////////////////
task performance_test;
//////////////////////////////////////////////////////////////////////////////////////   
   int 					    irq_counter;
   logic 				    irq_out_state;
   logic [23:0] 			    stream_wdata;
   logic [23:0] 			    stream_rdata;   
   int 					    cycle_counter;
   
   $info("performance_test");   

   // 1.
   reset_test;
   req_in = '0;

   // 2.
   stream_wdata = 1;
   irq_counter = 0;
   cycle_counter = 0;
   
   // 3.
   for (int i=0; i < AUDIO_FIFO_SIZE; ++i)
     begin
	wdata = stream_wdata;
	apb.write(LEFT_FIFO_ADDRESS, wdata, wfail);
	++stream_wdata;
	wdata = stream_wdata;	
	apb.write(RIGHT_FIFO_ADDRESS, wdata, wfail);
	++stream_wdata;
     end
   
   fork
      
      begin : host_process
	 // 4-1.1.
	 addr = CMD_REG_ADDRESS;
	 wdata = CMD_START;
	 apb.write(addr, wdata, wfail);
	 // 4-1.2.
	 while (irq_counter < 3)
	   begin
	      // 4-1.3.
	      irq.monitor(irq_out_state);
	      // 4-1.4.
	      if (!irq_out_state)
		begin
		   ++cycle_counter;
		   ia_performance_test_1: assert ( cycle_counter < (AUDIO_FIFO_SIZE+1) * CLK_DIV_48000 ) 
		     else
		       begin
			  assert_error("ia_performance_test_1");
			  irq_counter = 3;
		       end
		end
	      // 4-1.5.
	      else
		begin
		   for (int i=0; i < AUDIO_FIFO_SIZE; ++i)
		     begin
			wdata = stream_wdata;
			apb.write(LEFT_FIFO_ADDRESS, wdata, wfail);
			++stream_wdata;
			wdata = stream_wdata;		   
			apb.write(RIGHT_FIFO_ADDRESS, wdata, wfail);
			++stream_wdata;
		     end
		   
		   // 4-1.5.
		   addr = CMD_REG_ADDRESS;
		   wdata = CMD_IRQACK;
		   apb.write(addr, wdata, wfail);
		   irq_counter = irq_counter + 1;
		   cycle_counter = 0;
		end
	   end
	 
	 // 4-1.6.		 
	 addr = CMD_REG_ADDRESS;
	 wdata = CMD_STOP;
	 apb.write(addr, wdata, wfail);

      end : host_process

      begin : req_in_driver

	 // 4-2.1.
	 wait (play_out);
	 // 4-2.2.
	 while(play_out)
	   begin
	      repeat(CLK_DIV_48000-1) @(posedge clk);
	      req_in = '1;
	      @(posedge clk);	      
	      req_in = '0;
	   end
	 
      end : req_in_driver


      begin: audio_out_reader
	 // 4-3.1.
	 stream_rdata = 1;
	 // 4-3.2.
	 forever
	   begin
	      wait(tick_out);
	      ia_performance_test_2: assert ( (audio0_out == stream_rdata) && audio1_out == stream_rdata+1) else assert_error("ia_performance_test_2");
	      stream_rdata = stream_rdata + 2;
	      @(posedge clk);
	   end
	 
      end: audio_out_reader
   join_any
   disable fork;
   
   update_test_stats;      

endtask


