///////////////////////////////////////////////////////////
//
// control_unit_env
//
///////////////////////////////////////////////////////////

class control_unit_env extends uvm_env;
   `uvm_component_utils(control_unit_env)

   //-------------------------------------------------------- 
   // Member variables
   //--------------------------------------------------------
     

   //-------------------------------------------------------- 
   // Member functions
   //--------------------------------------------------------
   
   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);

   endfunction

   function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);

   endfunction
   
endclass   
