//=====================================================================
// Project: 4 core MESI cache design
// File Name: read_write_same_proc.sv
// Description: Test for read and then write on same processor
// Designers: Venky & Suru
//=====================================================================

class read_write_same_proc extends base_test;

    //component macro
    `uvm_component_utils(read_write_same_proc)

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", read_miss_icache_seq::type_id::get());
        super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Executing read_write_same_proc test" , UVM_LOW)
    endtask: run_phase

endclass : read_write_same_proc


// Sequence for a read and then write on same processor
class read_write_same_proc_seq extends base_vseq;
    //object macro
    `uvm_object_utils(read_miss_icache_seq5)

    int x;
    cpu_transaction_c trans;

    //constructor
    function new (string name="read_miss_icache_seq5");
        super.new(name);
    endfunction : new

    virtual task body();
    repeat(100)begin
	x=$urandom_range(0,3);
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[x], {request_type == READ_REQ;})
	    `uvm_do_on_with(trans, p_sequencer.cpu_seqr[x], {request_type == WRITE_REQ;})
	end
    endtask

endclass : read_write_same_proc_seq
