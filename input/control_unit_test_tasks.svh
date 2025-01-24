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
task address_decoding_test;
//////////////////////////////////////////////////////////////////////////////////////   
   $info("address_decoding_test");

   reset_test;
   req_in = '0;
   
   for (int i = 0; i < AUDIOPORT_REGISTERS; ++i) begin
      addr = AUDIOPORT_START_ADDRESS + i*4;
      wdata = $urandom;
      apb.write(addr, wdata, wfail);
      apb.read(addr, rdata, rfail);
   end

   addr = AUDIOPORT_END_ADDRESS + 4;
   wdata = $urandom;
   apb.write(addr, wdata, wfail);
   apb.read(addr, rdata, rfail);
   
   update_test_stats;

endtask

//////////////////////////////////////////////////////////////////////////////////////
task register_test;
//////////////////////////////////////////////////////////////////////////////////////
   $info("register_test");

   for (int i = 0; i < AUDIOPORT_REGISTERS; ++i) begin
	addr = AUDIOPORT_START_ADDRESS + i * 4;
	wdata = 0 + i;
	apb.write(addr, wdata, wfail);
	apb.read(addr, rdata, rfail);
	ia_register_test_1: assert (!wfail && !rfail && (wdata == rdata)) else 
        assert_error("ia_register_test1");
   end   

   addr = LEFT_FIFO_ADDRESS;
   wdata = $urandom & 24'hFFFFFF;
   apb.write(addr, wdata, wfail);
   apb.read(addr, rdata, rfail);

   addr = RIGHT_FIFO_ADDRESS;
   wdata = $urandom & 24'hFFFFFF;
   apb.write(addr, wdata, wfail);
   apb.read(addr, rdata, rfail);

   addr = AUDIOPORT_END_ADDRESS + 4;
   wdata = $urandom;
   apb.write(addr, wdata, wfail);
   apb.read(addr, rdata, rfail); 

   update_test_stats;

endtask


//////////////////////////////////////////////////////////////////////////////////////
task fifo_bus_test;
//////////////////////////////////////////////////////////////////////////////////////
   $info("fifo_bus_test");

   reset_test;
   req_in = '0;

   for (int i = 0; i < AUDIO_FIFO_SIZE; ++i) begin
	addr = LEFT_FIFO_ADDRESS;
	wdata = 0 + i;
	apb.write(addr, wdata, wfail);
   end

   for (int i = 0; i < AUDIO_FIFO_SIZE; ++i) begin
	addr = RIGHT_FIFO_ADDRESS;
	wdata = 2 + i;
	apb.write(addr, wdata, wfail);
   end

   for (int i = 0; i < AUDIO_FIFO_SIZE; ++i) begin
	addr = LEFT_FIFO_ADDRESS;
	apb.read(addr, rdata, rfail);
	ia_fifo_bus_test1: assert (!rfail && rdata == (0 + i)) else 
         assert_error("ia_fifo_bus_test_1");
   end

   for (int i = 0; i < AUDIO_FIFO_SIZE; ++i) begin
	addr = RIGHT_FIFO_ADDRESS;
	apb.read(addr, rdata, rfail);
	ia_fifo_bus_test2: assert (!rfail && rdata == (2 + i)) else 
         assert_error("ia_fifo_bus_test_2");
   end
 
   update_test_stats;
   
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

   reset_test;
   req_in = '0;

   addr = CMD_REG_ADDRESS;
   wdata = CMD_START;
   apb.write(addr, wdata, wfail);
   ia_start_stop_test1: assert (PLAY_OUT == '1 && STATUS_REG[STATUS_PLAY] == '1) else
    assert_error("ia_cmd_start_stop_test1");

   repeat(10)
    @(posedge clk);

   addr = CMD_REG_ADDRESS;
   wdata = CMD_STOP;
   apb.write(addr, wdata, wfail);
   ia_start_stop_test2: assert (PLAY:OUT == '0 && STATUS_REG[STATUS_PLAY] == '0) else
    assert_error("ia_cmd_start_stop_test2");

   update_test_stats;

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

   reset_test;
   req_in = '0;
   
   for (int i = 0; i < AUDIO_FIFO_SIZE; ++i) begin
	wdata = 320;
	apb.write(LEFT_FIFO_ADDRESS, wdata, wfail);
	apb.write(RIGHT_FIFO_ADDRESS, wdata, wfail);
   end

   addr = CMD_REG_ADDRESS;
   wdata = CMD_CLR;
   apb.write(addr, wdata, wfail);

   for (int i = 0; i < AUDIO_FIFO_SIZE; ++i) begin
	apb.read(LEFT_FIFO_ADDRESS, rdata, rfail);
	ia_cmd_clr_test_1: assert (rdata == 0) else 
         assert_error("ia_cmd_clr_test_1");

	apb.read(RIGHT_FIFO_ADDRESS, rdata, rfail);
	ia_cmd_clr_test2: assert (rdata == 0) else
	 assert_error("ia_cmd_clr_test2");
   end

   update_test_stats;

endtask


//////////////////////////////////////////////////////////////////////////////////////
task cmd_cfg_test;
//////////////////////////////////////////////////////////////////////////////////////   
   $info("cmd_cfg_test");

   reset_test;
   req_in = '0;

   addr = CMD_REG_ADDRESS;
   wdata = CMD_CFG;
   apb.write(addr, wdata, wfail);

   repeat(10)
	@(posedge clk);

   update_test_stats;

endtask


//////////////////////////////////////////////////////////////////////////////////////
task cmd_level_test;
//////////////////////////////////////////////////////////////////////////////////////   
   $info("cmd_level_test");

   reset_test;
   req_in = '0;

   addr = CMD_REG_ADDRESS;
   wdata = CMD_LEVEL;
   apb.write(addr, wdata, wfail);

   repeat(10)
	@(posedge clk);

   update_test_stats;

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

   reset_test;
   req_in = '0;

   fork
	begin : apb_control
	  addr = CMD_REG_ADDRESS;
	  wdata = CMD_START;
	  apb.write(addr, wdata, wfail);

	  repeat(50)
	    @(posedge clk);

	  addr = CMD_REG_ADDRESS;
	  wdata = CMD_STOP;
	  apb.write(addr, wdata, wfail);

	  repeat(50)
	    @(posedge clk);

	end : apb_control

	begin : req_writer
	  wait(play_out);
	    forever
		begin
		  repeat(10)
		    @(posedge clk);

		  req_in = '1;
		    @(posedge clk);
		  req_in = '0;
		  ia_req_tick_test_1: assert ((play_out && tick_out == '1) || (!play_out && tick_out == '0))
               		else assert_error("ia_req_tick_test_1: tick_out incorrect based on play_out state");
		end
	end : req_writer
   join_any
   disable fork;

   update_test_stats;

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


