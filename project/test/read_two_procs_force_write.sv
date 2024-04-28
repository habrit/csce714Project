//=====================================================================
// Project: 4 core MESI cache design
// File Name: read_two_procs_force_write.sv
// Description: Test to force an invalid state on cache
// Designers: Venky & Suru
//=====================================================================

class read_two_procs_force_write extends base_test;

    //component macro
    `uvm_component_utils(read_two_procs_force_write)

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", read_two_procs_force_write_seq::type_id::get());
        super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Executing read_two_procs_force_write test" , UVM_LOW)
    endtask: run_phase

endclass : read_two_procs_force_write


// Sequence for a read-miss on I-cache
class read_two_procs_force_write_seq extends base_vseq;
    //object macro
    `uvm_object_utils(read_two_procs_force_write_seq)

    cpu_transaction_c trans;

    bit[31:0] addr;
    rand bit[1:0] cpu_port1, cpu_port2;

    //constructor
    function new (string name="read_two_procs_force_write_seq");
        super.new(name);
    endfunction : new

    virtual task body();
    //Read on one proc, read on second proc, than write on second proc
repeat(100)begin
    `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'h41004100;})
	`uvm_do_on_with(trans, p_sequencer.cpu_seqr[3], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'h41004100;})
    `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'h41004100;})
end
   endtask

endclass : read_two_procs_force_write_seq
