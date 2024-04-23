//=====================================================================
// Project: 4 core MESI cache design
// File Name: read_miss_icache5.sv
// Description: Test for read-miss to I-cache
// Designers: Venky & Suru
//=====================================================================

class read_miss_icache5 extends base_test;

    //component macro
    `uvm_component_utils(read_miss_icache5)

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
        `uvm_info(get_type_name(), "Executing read_miss_icache5 test" , UVM_LOW)
    endtask: run_phase

endclass : read_miss_icache5


// Sequence for a read-miss on I-cache
class read_miss_icache_seq5 extends base_vseq;
    //object macro
    `uvm_object_utils(read_miss_icache_seq5)

    cpu_transaction_c trans;

    //constructor
    function new (string name="read_miss_icache_seq5");
        super.new(name);
    endfunction : new

    virtual task body();
    for (int i = 0; i < 4; i++) begin
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[i], {request_type == READ_REQ; access_cache_type == ICACHE_ACC;})
    end
    endtask

endclass : read_miss_icache_seq5
