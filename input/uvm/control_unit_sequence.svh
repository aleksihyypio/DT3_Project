///////////////////////////////////////////////////////////
// control_unit_sequence
///////////////////////////////////////////////////////////

class control_unit_sequence extends uvm_sequence #(apb_transaction);
      `uvm_object_utils(control_unit_sequence)

   //-------------------------------------------------------- 
   // Member functions
   //--------------------------------------------------------
	
   function new (string name = "");
      super.new(name);
   endfunction

   
   task body;

      /////////////////////////////////////////////////////////////////////
      // Variable declarations
      /////////////////////////////////////////////////////////////////////      

      uvm_event                 irq_event;

      /////////////////////////////////////////////////////////////////////      
      // Executable code
      /////////////////////////////////////////////////////////////////////

      reset_test_stats;       
      irq_event = uvm_event_pool::get_global("irq_out");

      //    Example: You can wait for the irq_event like this:
      //    irq_event.wait_trigger();





      
   endtask

   //----------------------------------------------------------------
   // Notice! This sequence can only access the control_unit's APB
   //         bus ports. Therefore the test program functions that need
   //         access to other ports are not implemented.
   //-----------------------------------------------------------------

endclass 
