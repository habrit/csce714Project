//=====================================================================
// Project: 4 core MESI cache design
// File Name: ex_to_invalid.sv
// Description: Test for Exclusive state to other states
// Designers: Venky & Suru
//=====================================================================

class ex_to_invalid extends base_test;

    //component macro
    `uvm_component_utils(ex_to_invalid)

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", ex_to_invalid_seq::type_id::get());
        super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Executing ex_to_invalid test" , UVM_LOW)
    endtask: run_phase

endclass : ex_to_invalid

// Sequence for a read-hit on D-cache
class ex_to_invalid_seq extends base_vseq;
    //object macro
    `uvm_object_utils(ex_to_invalid_seq)

    cpu_transaction_c trans;

    //constructor
    function new (string name="ex_to_invalid_seq");
        super.new(name);
    endfunction : new

    virtual task body();
	//exclusive to invalid
	`uvm_do_on_with(trans, p_sequencer.cpu_seqr[2], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'h5004AAAC;})
	`uvm_do_on_with(trans, p_sequencer.cpu_seqr[3], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'h5004AAAC;})
	`uvm_do_on_with(trans, p_sequencer.cpu_seqr[2], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'h5004AAAC;})
    endtask

endclass : ex_to_invalid_seq


