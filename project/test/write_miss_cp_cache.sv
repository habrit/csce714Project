//=====================================================================
// Project: 4 core MESI cache design
// File Name: write_miss_cp_cache.sv
// Description: Test for read-miss to I-cache
// Designers: Venky & Suru
//=====================================================================

class write_miss_cp_cache extends base_test;

    //component macro
    `uvm_component_utils(write_miss_cp_cache)

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", write_miss_cp_cache_seq::type_id::get());
        super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Executing write_miss_cp_cache test" , UVM_LOW)
    endtask: run_phase

endclass : write_miss_cp_cache


// Sequence for a read-miss on I-cache
class write_miss_cp_cache_seq extends base_vseq;
    //object macro
    `uvm_object_utils(write_miss_cp_cache_seq)

    cpu_transaction_c trans;

    //constructor
    function new (string name="write_miss_cp_cache_seq");
        super.new(name);
    endfunction : new

    virtual task body();
	int addr = 32'h50005000;
	for(int z=0;z<4;z++)
	begin
	if(z<3) begin
	`uvm_do_on_with(trans, p_sequencer.cpu_seqr[z+1], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == addr;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[z], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC;address == addr;})
	end
	else begin
	`uvm_do_on_with(trans, p_sequencer.cpu_seqr[z-1], {request_type == READ_REQ; access_cache_type == DCACHE_ACC;address == addr;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[z], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC;address == addr;})
	end
	addr = addr + 32'h00010000;
	end
    endtask

endclass : write_miss_cp_cache_seq
