//=====================================================================
// Project: 4 core MESI cache design
// File Name: write_miss_replacement_shared
// Description: Test for write miss to shared cache
// Designers: Venky & Suru
//=====================================================================

class write_miss_replacement_shared extends base_test;

    //component macro
    `uvm_component_utils(write_miss_replacement_shared)

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", write_miss_replacement_shared_seq::type_id::get());
        super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Executing write_miss_replacement_shared test" , UVM_LOW)
    endtask: run_phase

endclass : write_miss_replacement_shared


class write_miss_replacement_shared_seq extends base_vseq;
    //object macro
    `uvm_object_utils(write_miss_replacement_shared_seq)
rand int cpu_port;
    cpu_transaction_c trans;

    //constructor
    function new (string name="write_miss_replacement_shared_seq");
        super.new(name);
    endfunction : new

    virtual task body();
//  repeat(4)
// begin
   //cpu_port = $urandom_range(0,3);
`uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; address == 32'h4000_0000; })
`uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; address == 32'h4011_0000; })
`uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; address == 32'h4022_0000;})
`uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; address == 32'h4033_0000; })
`uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == WRITE_REQ; address == 32'h4044_0000; })
`uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == WRITE_REQ; address == 32'h4044_0000; })
   `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == WRITE_REQ; address == 32'h4011_0000; })
   `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == WRITE_REQ; address == 32'h4022_0000; })
 //  `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == WRITE_REQ; address == 32'h40_0000; })
//  end
    endtask
endclass:write_miss_replacement_shared_seq

