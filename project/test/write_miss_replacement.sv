class write_miss_replacement extends base_test;
  
  //component macro
  `uvm_component_utils(write_miss_replacement)
  
  //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
          uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", write_miss_replacement_seq::type_id::get());
        super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Executing write_miss_replacement test" , UVM_LOW)
    endtask: run_phase
    
endclass : write_miss_replacement

class write_miss_replacement_seq extends base_vseq;
    //object macro
    `uvm_object_utils(write_miss_replacement_seq)

    cpu_transaction_c trans;

    //constructor
    function new (string name="write_miss_replacement_seq");
        super.new(name);
    endfunction : new

    virtual task body();
    
        for(int z=0;z<4;z++)
        begin
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[z], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address ==32'h5000_AAAC; })
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[z], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address ==32'h5001_AAAC; })
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[z], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address ==32'h5002_AAAC; })
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[z], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address ==32'h5003_AAAC; })
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[z], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address ==32'h5004_AAAC; })
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[z], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address ==32'h5000_AAAC; })
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[z], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address ==32'h5001_AAAC; })
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[z], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address ==32'h5002_AAAC; })
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[z], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address ==32'h5003_AAAC; })
        end
    endtask

endclass : write_miss_replacement_seq


