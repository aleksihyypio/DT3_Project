///////////////////////////////////////////////////////////
//
// control_unit_agent
//
///////////////////////////////////////////////////////////

class control_unit_agent extends uvm_agent;
   `uvm_component_utils(control_unit_agent)

   //-------------------------------------------------------- 
   // Member variables
   //--------------------------------------------------------
     
   uvm_event m_irq_event;
   
   //-------------------------------------------------------- 
   // Member functions
   //--------------------------------------------------------
   
   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      m_irq_event = uvm_event_pool::get_global("irq_out");

   endfunction

   function void connect_phase(uvm_phase phase);

   endfunction

   function void write(irq_transaction t);
      if(t.irq)
	m_irq_event.trigger();
   endfunction

endclass
 
