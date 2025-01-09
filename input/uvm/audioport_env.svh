///////////////////////////////////////////////////////////
//
// audioport_env
//
///////////////////////////////////////////////////////////

class audioport_env extends uvm_env;
   `uvm_component_utils(audioport_env)

   // Member variables

   // Member functions

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

