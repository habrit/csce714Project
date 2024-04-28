//=====================================================================
// Project: 4 core MESI cache design
// File Name: fsm_exclusive_to_others.sv
// Description: Test for Exclusive state to other states
// Designers: Venky & Suru
//=====================================================================

class fsm_exclusive_to_others extends base_test;

    //component macro
    `uvm_component_utils(fsm_exclusive_to_others)

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", fsm_exclusive_to_others_seq::type_id::get());
        super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Executing fsm_exclusive_to_others test" , UVM_LOW)
    endtask: run_phase

endclass : fsm_exclusive_to_others

// Sequence for a read-hit on D-cache
class fsm_exclusive_to_others_seq extends base_vseq;
    //object macro
    `uvm_object_utils(fsm_exclusive_to_others_seq)

    cpu_transaction_c trans;

    //constructor
    function new (string name="fsm_exclusive_to_others_seq");
        super.new(name);
    endfunction : new

    virtual task body();
	//exclusive to modified
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'h5000AAAC;})
	`uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'h5000AAAC;})
	//exclusive to shared
	`uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'h5002AAAC;})
	`uvm_do_on_with(trans, p_sequencer.cpu_seqr[2], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'h5002AAAC;})
	`uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'h5002AAAC;})
	//exclusive to invalid
	`uvm_do_on_with(trans, p_sequencer.cpu_seqr[2], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'h5004AAAC;})
	`uvm_do_on_with(trans, p_sequencer.cpu_seqr[3], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'h5004AAAC;})
	`uvm_do_on_with(trans, p_sequencer.cpu_seqr[2], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'h5004AAAC;})
    endtask

endclass : fsm_exclusive_to_others_seq


