///////////////////////////////////////////////////////////
//
// control_unit_uvm_test
//
///////////////////////////////////////////////////////////
   
class control_unit_uvm_test extends uvm_test;
  `uvm_component_utils(control_unit_uvm_test)

   //-------------------------------------------------------- 
   // Member variables
   //--------------------------------------------------------
    

   //-------------------------------------------------------- 
   // Member functions
   //--------------------------------------------------------
    
   function new(string name, uvm_component parent);
      super.new(name,parent);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      
   endfunction: build_phase
   
   task run_phase(uvm_phase phase);
      // Local variables

      // Executable code
      reset_test_stats; 




      
      update_test_stats;      
      $display("#####################################################################################################");	
      $display("control_uvm_test results: PASSED: %d / FAILED: %d", tests_passed, tests_failed);
      $display("#####################################################################################################");	

      ia_control_unit_uvm_test: assert (tests_failed == 0) else 
	assert_error("ia_control_unit_uvm_test");  // See audioport_pkg.sv
      
    endtask

endclass 
