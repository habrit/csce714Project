//=====================================================================
// Project: 4 core MESI cache design
// File Name: cpu_monitor_c.sv
// Description: cpu monitor component
// Designers: Venky & Suru
//=====================================================================

class cpu_monitor_c extends uvm_monitor;
    //component macro
    `uvm_component_utils(cpu_monitor_c)
    cpu_mon_packet_c packet;
    uvm_analysis_port #(cpu_mon_packet_c) mon_out;

    // Virtual interface of used to drive and observe CPU-LV1 interface signals
    virtual interface cpu_lv1_interface vi_cpu_lv1_if;

    virtual interface cpu_mesi_lru_interface mesi_state_if;
    parameter INVALID   = 3'b000;
    parameter SHARED    = 3'b001;
    parameter EXCLUSIVE = 3'b010;
    parameter MODIFIED  = 3'b011;

    bit [1 : 0]       c_mesi_proc;                                                   
    bit [1 : 0]       u_mesi_proc;
    bit [2 : 0]       lru_var;
    bit [1 : 0]       blk_accessed_main;
    bit [1 : 0]       lru_replacement_proc;
    bit		      blk_hit_proc;
    bit		      blk_free;
    bit   [1:0]       proc_id;

    covergroup cover_cpu_packet;
        option.per_instance = 1;
        option.name = "cover_cpu_packets";
        REQUEST: coverpoint packet.request_type;
        //TODO: add coverpoints for Data, Address, etc.
		DATA: coverpoint packet.dat{
                option.auto_bin_max = 20;
        }
        ADDRESS: coverpoint packet.address{
                option.auto_bin_max = 20;
        }
        ADDRESS_TYPE: coverpoint packet.addr_type;
        NUMCYCLES: coverpoint packet.num_cycles;
        ILLEGAL: coverpoint packet.illegal;
		
		X_TYPE__DATA: cross REQUEST, DATA;
        X_TYPE__ADDR: cross REQUEST, ADDRESS;
        X_TYPE__ADDRTYPE: cross REQUEST, ADDRESS_TYPE{
		ignore_bins ignore_icache_write = binsof(REQUEST) intersect {WRITE_REQ} && binsof(ADDRESS_TYPE) intersect {ICACHE};}
		
    endgroup

    covergroup cover_mesi_proc0;
	option.per_instance = 1;
	option.name = "cover_mesi_proc0";
	MESI_C0_P: coverpoint c_mesi_proc{
        bins BIN_PC0_INVALID   = INVALID;
        bins BIN_PC0_SHARED    = SHARED;
        bins BIN_PC0_EXCLUSIVE = EXCLUSIVE;
        bins BIN_PC0_MODIFIED  = MODIFIED;            
	} 

	MESI_U0_P: coverpoint u_mesi_proc{ 
        bins BIN_PU0_INVALID   = {INVALID};
        bins BIN_PU0_SHARED    = {SHARED};
        bins BIN_PU0_EXCLUSIVE = {EXCLUSIVE};
        bins BIN_PU0_MODIFIED  = {MODIFIED};
	} 

	MESI_C0_TRANS: coverpoint c_mesi_proc{
	bins TRANS1_A = (MODIFIED => MODIFIED) iff (u_mesi_proc == MODIFIED);
	bins TRANS2_A = (EXCLUSIVE => MODIFIED) iff (u_mesi_proc == MODIFIED); 
	bins TRANS3_A = (EXCLUSIVE => EXCLUSIVE) iff (u_mesi_proc == EXCLUSIVE); 
	bins TRANS4_A = (SHARED => MODIFIED) iff (u_mesi_proc == MODIFIED);
	bins TRANS5_A = (SHARED => SHARED) iff (u_mesi_proc == SHARED);
	bins TRANS6_A = (INVALID => MODIFIED) iff (u_mesi_proc == MODIFIED);
	bins TRANS7_A = (INVALID => SHARED) iff (u_mesi_proc == SHARED);
	bins TRANS8_A = (INVALID => EXCLUSIVE) iff (u_mesi_proc == EXCLUSIVE);
	}
    endgroup
    
    covergroup cover_mesi_proc1;
	option.per_instance = 1;
	option.name = "cover_mesi_proc1";
	MESI_C1_P: coverpoint c_mesi_proc{
        bins BIN_PC1_INVALID   = INVALID;
        bins BIN_PC1_SHARED    = SHARED;
        bins BIN_PC1_EXCLUSIVE = EXCLUSIVE;
        bins BIN_PC1_MODIFIED  = MODIFIED;            
	} 

	MESI_U1_P: coverpoint u_mesi_proc{ 
        bins BIN_PU1_INVALID   = {INVALID};
        bins BIN_PU1_SHARED    = {SHARED};
        bins BIN_PU1_EXCLUSIVE = {EXCLUSIVE};
        bins BIN_PU1_MODIFIED  = {MODIFIED};
	} 

	MESI_C1_TRANS: coverpoint c_mesi_proc{
	bins TRANS1_B = (MODIFIED => MODIFIED) iff (u_mesi_proc == MODIFIED);
	bins TRANS2_B = (EXCLUSIVE => MODIFIED) iff (u_mesi_proc == MODIFIED); 
	bins TRANS3_B = (EXCLUSIVE => EXCLUSIVE) iff (u_mesi_proc == EXCLUSIVE); 
	bins TRANS4_B = (SHARED => MODIFIED) iff (u_mesi_proc == MODIFIED);
	bins TRANS5_B = (SHARED => SHARED) iff (u_mesi_proc == SHARED);
	bins TRANS6_B = (INVALID => MODIFIED) iff (u_mesi_proc == MODIFIED);
	bins TRANS7_B = (INVALID => SHARED) iff (u_mesi_proc == SHARED);
	bins TRANS8_B = (INVALID => EXCLUSIVE) iff (u_mesi_proc == EXCLUSIVE);
	}
    endgroup
    
    covergroup cover_mesi_proc2;
	option.per_instance = 1;
	option.name = "cover_mesi_proc2";
	MESI_C2_P: coverpoint c_mesi_proc{
        bins BIN_PC2_INVALID   = INVALID;
        bins BIN_PC2_SHARED    = SHARED;
        bins BIN_PC2_EXCLUSIVE = EXCLUSIVE;
        bins BIN_PC2_MODIFIED  = MODIFIED;            
	} 

	MESI_U2_P: coverpoint u_mesi_proc{ 
        bins BIN_PU2_INVALID   = {INVALID};
        bins BIN_PU2_SHARED    = {SHARED};
        bins BIN_PU2_EXCLUSIVE = {EXCLUSIVE};
        bins BIN_PU2_MODIFIED  = {MODIFIED};
	} 

	MESI_C2_TRANS: coverpoint c_mesi_proc{
	bins TRANS1_C = (MODIFIED => MODIFIED) iff (u_mesi_proc == MODIFIED);
	bins TRANS2_C = (EXCLUSIVE => MODIFIED) iff (u_mesi_proc == MODIFIED); 
	bins TRANS3_C = (EXCLUSIVE => EXCLUSIVE) iff (u_mesi_proc == EXCLUSIVE); 
	bins TRANS4_C = (SHARED => MODIFIED) iff (u_mesi_proc == MODIFIED);
	bins TRANS5_C = (SHARED => SHARED) iff (u_mesi_proc == SHARED);
	bins TRANS6_C = (INVALID => MODIFIED) iff (u_mesi_proc == MODIFIED);
	bins TRANS7_C = (INVALID => SHARED) iff (u_mesi_proc == SHARED);
	bins TRANS8_C = (INVALID => EXCLUSIVE) iff (u_mesi_proc == EXCLUSIVE);
	}
    endgroup
    
    covergroup cover_mesi_proc3;
	option.per_instance = 1;
	option.name = "cover_mesi_proc3";
	MESI_C3_P: coverpoint c_mesi_proc{
        bins BIN_PC3_INVALID   = INVALID;
        bins BIN_PC3_SHARED    = SHARED;
        bins BIN_PC3_EXCLUSIVE = EXCLUSIVE;
        bins BIN_PC3_MODIFIED  = MODIFIED;            
	} 

	MESI_U3_P: coverpoint u_mesi_proc{ 
        bins BIN_PU3_INVALID   = {INVALID};
        bins BIN_PU3_SHARED    = {SHARED};
        bins BIN_PU3_EXCLUSIVE = {EXCLUSIVE};
        bins BIN_PU3_MODIFIED  = {MODIFIED};
	} 

	MESI_C3_TRANS: coverpoint c_mesi_proc{
	bins TRANS1_D = (MODIFIED => MODIFIED) iff (u_mesi_proc == MODIFIED);
	bins TRANS2_D = (EXCLUSIVE => MODIFIED) iff (u_mesi_proc == MODIFIED); 
	bins TRANS3_D = (EXCLUSIVE => EXCLUSIVE) iff (u_mesi_proc == EXCLUSIVE); 
	bins TRANS4_D = (SHARED => MODIFIED) iff (u_mesi_proc == MODIFIED);
	bins TRANS5_D = (SHARED => SHARED) iff (u_mesi_proc == SHARED);
	bins TRANS6_D = (INVALID => MODIFIED) iff (u_mesi_proc == MODIFIED);
	bins TRANS7_D = (INVALID => SHARED) iff (u_mesi_proc == SHARED);
	bins TRANS8_D = (INVALID => EXCLUSIVE) iff (u_mesi_proc == EXCLUSIVE);
	}
    endgroup

    covergroup cover_group_lru;
	option.per_instance = 1;
	option.name = "cover_lru";

	REPLACE_PROC: coverpoint lru_replacement_proc iff (~blk_hit_proc & ~blk_free);
	ACCESS_MAIN1: coverpoint blk_accessed_main iff blk_hit_proc;
	ACCESS_MAIN2: coverpoint blk_accessed_main iff blk_free;
	ACCESS_MAIN3: coverpoint blk_accessed_main iff (~blk_hit_proc & ~blk_free);
	LRU_VAR: coverpoint lru_var;
	
	X_PROC_LRU1: cross ACCESS_MAIN1, LRU_VAR iff blk_hit_proc{
	bins LRU1_1A = binsof(ACCESS_MAIN1) intersect{2'b00} && binsof(LRU_VAR) intersect{3'b111} ;
	bins LRU1_2A = binsof(ACCESS_MAIN1) intersect{2'b00} && binsof(LRU_VAR) intersect{3'b110} ;
	bins LRU2_1A = binsof(ACCESS_MAIN1) intersect{2'b01} && binsof(LRU_VAR) intersect{3'b101} ;
	bins LRU2_2A = binsof(ACCESS_MAIN1) intersect{2'b01} && binsof(LRU_VAR) intersect{3'b100} ;
	bins LRU3_1A = binsof(ACCESS_MAIN1) intersect{2'b10} && binsof(LRU_VAR) intersect{3'b011} ;
	bins LRU3_2A = binsof(ACCESS_MAIN1) intersect{2'b10} && binsof(LRU_VAR) intersect{3'b001} ;
	bins LRU4_1A = binsof(ACCESS_MAIN1) intersect{2'b11} && binsof(LRU_VAR) intersect{3'b010} ;
	bins LRU4_2A = binsof(ACCESS_MAIN1) intersect{2'b11} && binsof(LRU_VAR) intersect{3'b000} ;
	ignore_bins LRU4A_ignore = binsof(ACCESS_MAIN1) intersect{2'b11} && binsof(LRU_VAR) intersect{3'b110,3'b001,3'b111,3'b011,3'b100,3'b101} ;
	ignore_bins LRU1A_ignore = binsof(ACCESS_MAIN1) intersect{2'b00} && binsof(LRU_VAR) intersect{3'b000,3'b001,3'b010,3'b011,3'b100,3'b101} ;
	ignore_bins LRU2A_ignore = binsof(ACCESS_MAIN1) intersect{2'b01} && binsof(LRU_VAR) intersect{3'b000,3'b001,3'b010,3'b011,3'b110,3'b111} ;
	ignore_bins LRU3A_ignore = binsof(ACCESS_MAIN1) intersect{2'b10} && binsof(LRU_VAR) intersect{3'b000,3'b110,3'b010,3'b111,3'b100,3'b101} ;
	}

	X_PROC_LRU2: cross ACCESS_MAIN2, LRU_VAR iff blk_free{
	bins LRU1_1B = binsof(ACCESS_MAIN2) intersect{2'b00} && binsof(LRU_VAR) intersect{3'b111} ;
	bins LRU1_2B = binsof(ACCESS_MAIN2) intersect{2'b00} && binsof(LRU_VAR) intersect{3'b110} ;
	bins LRU2_1B = binsof(ACCESS_MAIN2) intersect{2'b01} && binsof(LRU_VAR) intersect{3'b101} ;
	bins LRU2_2B = binsof(ACCESS_MAIN2) intersect{2'b01} && binsof(LRU_VAR) intersect{3'b100} ;
	bins LRU3_1B = binsof(ACCESS_MAIN2) intersect{2'b10} && binsof(LRU_VAR) intersect{3'b011} ;
	bins LRU3_2B = binsof(ACCESS_MAIN2) intersect{2'b10} && binsof(LRU_VAR) intersect{3'b001} ;
	bins LRU4_1B = binsof(ACCESS_MAIN2) intersect{2'b11} && binsof(LRU_VAR) intersect{3'b010} ;
	bins LRU4_2B = binsof(ACCESS_MAIN2) intersect{2'b11} && binsof(LRU_VAR) intersect{3'b000} ;
	ignore_bins LRU4B_ignore = binsof(ACCESS_MAIN2) intersect{2'b11} && binsof(LRU_VAR) intersect{3'b110,3'b001,3'b111,3'b011,3'b100,3'b101} ;
	ignore_bins LRU1B_ignore = binsof(ACCESS_MAIN2) intersect{2'b00} && binsof(LRU_VAR) intersect{3'b000,3'b001,3'b010,3'b011,3'b100,3'b101} ;
	ignore_bins LRU2B_ignore = binsof(ACCESS_MAIN2) intersect{2'b01} && binsof(LRU_VAR) intersect{3'b000,3'b001,3'b010,3'b011,3'b110,3'b111} ;
	ignore_bins LRU3B_ignore = binsof(ACCESS_MAIN2) intersect{2'b10} && binsof(LRU_VAR) intersect{3'b000,3'b110,3'b010,3'b111,3'b100,3'b101} ;
	}

	X_PROC_LRU3: cross ACCESS_MAIN3, LRU_VAR iff (~blk_hit_proc & ~blk_free){
	bins LRU1_1C = binsof(ACCESS_MAIN3) intersect{2'b00} && binsof(LRU_VAR) intersect{3'b111} ;
	bins LRU1_2C = binsof(ACCESS_MAIN3) intersect{2'b00} && binsof(LRU_VAR) intersect{3'b110} ;
	bins LRU2_1C = binsof(ACCESS_MAIN3) intersect{2'b01} && binsof(LRU_VAR) intersect{3'b101} ;
	bins LRU2_2C = binsof(ACCESS_MAIN3) intersect{2'b01} && binsof(LRU_VAR) intersect{3'b100} ;
	bins LRU3_1C = binsof(ACCESS_MAIN3) intersect{2'b10} && binsof(LRU_VAR) intersect{3'b011} ;
	bins LRU3_2C = binsof(ACCESS_MAIN3) intersect{2'b10} && binsof(LRU_VAR) intersect{3'b001} ;
	bins LRU4_1C = binsof(ACCESS_MAIN3) intersect{2'b11} && binsof(LRU_VAR) intersect{3'b010} ;
	bins LRU4_2C = binsof(ACCESS_MAIN3) intersect{2'b11} && binsof(LRU_VAR) intersect{3'b000} ;
	ignore_bins LRU4C_ignore = binsof(ACCESS_MAIN3) intersect{2'b11} && binsof(LRU_VAR) intersect{3'b110,3'b001,3'b111,3'b011,3'b100,3'b101} ;
	ignore_bins LRU1C_ignore = binsof(ACCESS_MAIN3) intersect{2'b00} && binsof(LRU_VAR) intersect{3'b000,3'b001,3'b010,3'b011,3'b100,3'b101} ;
	ignore_bins LRU2C_ignore = binsof(ACCESS_MAIN3) intersect{2'b01} && binsof(LRU_VAR) intersect{3'b000,3'b001,3'b010,3'b011,3'b110,3'b111} ;
	ignore_bins LRU3C_ignore = binsof(ACCESS_MAIN3) intersect{2'b10} && binsof(LRU_VAR) intersect{3'b000,3'b110,3'b010,3'b111,3'b100,3'b101} ;
	}
    endgroup


    //constructor
    function new (string name, uvm_component parent);
        super.new(name, parent);
        mon_out = new ("mon_out", this);
        this.cover_cpu_packet = new();
        this.cover_mesi_proc0 = new();
        this.cover_mesi_proc1 = new();
        this.cover_mesi_proc2 = new();
        this.cover_mesi_proc3 = new();
        this.cover_group_lru = new();
    endfunction : new

    //UVM build phase ()
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        // throw error if virtual interface is not set
        if (!uvm_config_db#(virtual cpu_lv1_interface)::get(this, "","vif", vi_cpu_lv1_if))
            `uvm_fatal("NO_VIF",{"virtual interface must be set for: ",get_full_name(),".vif"})
        if (!uvm_config_db#(virtual cpu_mesi_lru_interface)::get(this, "","mesi_if", mesi_state_if))
            `uvm_fatal("NO_VIF",{"virtual interface must be set for: ",get_full_name(),".mesi_if"})
    endfunction: build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "RUN Phase", UVM_LOW)
        forever begin
            //TODO: Code for the CPU monitor is incomplete
            //Add code to populate other fields of the cpu monitor packet
            //Ensure that your code can handle all possible cases (read, write
            //etc)
            @(posedge vi_cpu_lv1_if.cpu_rd or posedge vi_cpu_lv1_if.cpu_wr)
            packet = cpu_mon_packet_c::type_id::create("packet", this);
            if(vi_cpu_lv1_if.cpu_rd === 1'b1) begin
                packet.request_type = READ_REQ;
            end
            else begin
                packet.request_type = WRITE_REQ;
            end

            packet.address = vi_cpu_lv1_if.addr_bus_cpu_lv1; 
            cover_cpu_packet.sample();

            if(packet.address < 32'h4000_0000) begin
                packet.addr_type = ICACHE;
            end
            else begin
                packet.addr_type = DCACHE;
	    end
	    if( packet.addr_type == ICACHE && packet.request_type == WRITE_REQ) begin
              packet.illegal = 1'b1;
            end

	    fork 
		begin: lru_coverage
			forever begin
			@(posedge mesi_state_if.clk)
	    			blk_free = mesi_state_if.blk_free;
	    			blk_hit_proc = mesi_state_if.blk_hit_proc;
	    			lru_var = mesi_state_if.lru_var;
	    			blk_accessed_main = mesi_state_if.blk_accessed_main;
	    			lru_replacement_proc = mesi_state_if.lru_replacement_proc;
	    			lru_replacement_proc = mesi_state_if.lru_replacement_proc;
            			`uvm_info(get_type_name(), $sformatf("LRU lru_replacement_proc = %b, blk_hit_proc = %b,blk_free = %b",lru_replacement_proc,blk_hit_proc,blk_free), UVM_HIGH)
            			//`uvm_info(get_type_name(), $sformatf("DEBUG= %b", ~blk_hit_proc & ~blk_free), UVM_LOW)
            			cover_group_lru.sample(); 
			end
			
		end: lru_coverage
		begin: mesi_coverage
			proc_id = mesi_state_if.proc_id;
			forever begin
			@(posedge mesi_state_if.clk)
				if(proc_id == 'b00) begin
	    			c_mesi_proc = mesi_state_if.current_mesi_proc;
	    			u_mesi_proc = mesi_state_if.updated_mesi_proc;
            			`uvm_info(get_type_name(), $sformatf("Mesi curr = %d, update = %d",c_mesi_proc,u_mesi_proc), UVM_HIGH)
            			cover_mesi_proc0.sample(); 
				end
				if(proc_id == 'b01) begin
	    			c_mesi_proc = mesi_state_if.current_mesi_proc;
	    			u_mesi_proc = mesi_state_if.updated_mesi_proc;
            			`uvm_info(get_type_name(), $sformatf("Mesi curr = %d, update = %d",c_mesi_proc,u_mesi_proc), UVM_HIGH)
            			cover_mesi_proc1.sample(); 
				end
				if(proc_id == 'b10) begin
	    			c_mesi_proc = mesi_state_if.current_mesi_proc;
	    			u_mesi_proc = mesi_state_if.updated_mesi_proc;
            			`uvm_info(get_type_name(), $sformatf("Mesi curr = %d, update = %d",c_mesi_proc,u_mesi_proc), UVM_HIGH)
            			cover_mesi_proc2.sample(); 
				end
				if(proc_id == 'b11) begin
	    			c_mesi_proc = mesi_state_if.current_mesi_proc;
	    			u_mesi_proc = mesi_state_if.updated_mesi_proc;
            			`uvm_info(get_type_name(), $sformatf("Mesi curr = %d, update = %d",c_mesi_proc,u_mesi_proc), UVM_HIGH)
            			cover_mesi_proc3.sample(); 
				end
			end
		end:mesi_coverage
	    join_none

            @(posedge vi_cpu_lv1_if.data_in_bus_cpu_lv1 or posedge vi_cpu_lv1_if.cpu_wr_done)
            packet.dat = vi_cpu_lv1_if.data_bus_cpu_lv1;
            cover_cpu_packet.sample();

            @(negedge vi_cpu_lv1_if.cpu_rd or negedge vi_cpu_lv1_if.cpu_wr)
            mon_out.write(packet);
            cover_cpu_packet.sample();
        end
    endtask : run_phase

endclass : cpu_monitor_c
