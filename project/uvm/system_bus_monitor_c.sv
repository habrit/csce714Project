//=====================================================================
// Project: 4 core MESI cache design
// File Name: system_bus_monitor_c.sv
// Description: system bus monitor component
// Designers: Venky & Suru
//=====================================================================

`include "sbus_packet_c.sv"

class system_bus_monitor_c extends uvm_monitor;
    //component macro
    `uvm_component_utils(system_bus_monitor_c)

    uvm_analysis_port #(sbus_packet_c) sbus_out;
    sbus_packet_c       s_packet;

    parameter INVALID   = 3'b000;
    parameter SHARED    = 3'b001;
    parameter EXCLUSIVE = 3'b010;
    parameter MODIFIED  = 3'b011;

    bit [1 : 0]       c_mesi_snoop0;                                                   
    bit [1 : 0]       u_mesi_snoop0;
    bit [1 : 0]       c_mesi_snoop1;                                                   
    bit [1 : 0]       u_mesi_snoop1;
    bit [1 : 0]       c_mesi_snoop2;                                                   
    bit [1 : 0]       u_mesi_snoop2;
    bit [1 : 0]       c_mesi_snoop3;                                                   
    bit [1 : 0]       u_mesi_snoop3;

    //Covergroup to monitor all the points within sbus_packet
    covergroup cover_sbus_packet;
        option.per_instance = 1;
        option.name = "cover_system_bus";
        REQUEST_TYPE: coverpoint  s_packet.bus_req_type;
        REQUEST_PROCESSOR: coverpoint s_packet.bus_req_proc_num;
        REQUEST_ADDRESS: coverpoint s_packet.req_address{
            option.auto_bin_max = 10;
        }
        READ_DATA: coverpoint s_packet.rd_data{
            option.auto_bin_max = 10;
        }
        //TODO: Add coverage for other fields of sbus_mon_packet		
		
		WRITE_DATA_SNOOP: coverpoint s_packet.wr_data_snoop{
            option.auto_bin_max = 10;
        }
		
		BUS_REQUEST_SNOOP: coverpoint  s_packet.bus_req_snoop;
		SNOOP_WRITE_REQUEST_FLAG: coverpoint s_packet.snoop_wr_req_flag;
		
		// checking all the level 2 accesses 
		REQUEST_SERVICED_BY: coverpoint  s_packet.req_serviced_by{
           ignore_bins ignore_req_serviced_by = {SERV_SNOOP0, SERV_SNOOP1, SERV_SNOOP2, SERV_SNOOP3};
	}

		COPY_IN_CACHE: coverpoint s_packet.cp_in_cache;
		SHARED: coverpoint s_packet.shared;
		
		
		PROC_EVICT_DIRTY_BLK_ADDR: coverpoint s_packet.proc_evict_dirty_blk_addr{
           option.auto_bin_max = 10;
        }
        PROC_EVICT_DIRTY_BLK_DATA: coverpoint s_packet.proc_evict_dirty_blk_data{
           option.auto_bin_max = 10;
        }
        PROC_EVICT_DIRTY_BLK_FLAG: coverpoint s_packet.proc_evict_dirty_blk_flag;



        //cross coverage
        //ensure each processor has read miss, write miss, invalidate, etc.
        X_PROC__REQ_TYPE: cross REQUEST_TYPE, REQUEST_PROCESSOR;
        X_PROC__ADDRESS: cross REQUEST_PROCESSOR, REQUEST_ADDRESS;
        X_PROC__DATA: cross REQUEST_PROCESSOR, READ_DATA;
        //TODO: Add relevant cross coverage (examples shown above)

		// request number and write data 
		X_PROC__WR_DATA: cross REQUEST_PROCESSOR, WRITE_DATA_SNOOP;
        
		//requested number and snoop
		X_PROC__SNOOP: cross REQUEST_PROCESSOR, BUS_REQUEST_SNOOP;
		
		//request and serviced by cross
		X_PROC__SERVICED_BY: cross REQUEST_PROCESSOR, REQUEST_SERVICED_BY;

    endgroup

    covergroup cover_mesi_snoop0;
	option.per_instance = 1;
        option.name = "cover_mesi_s0";
	MESI_C0_S: coverpoint c_mesi_snoop0{
        bins BIN_SC0_INVALID   = INVALID;
        bins BIN_SC0_SHARED    = SHARED;
        bins BIN_SC0_EXCLUSIVE = EXCLUSIVE;
        bins BIN_SC0_MODIFIED  = MODIFIED;            
	} 
	MESI_U0_S: coverpoint u_mesi_snoop0{ 
        bins BIN_SU0_INVALID   = INVALID;
        bins BIN_SU0_SHARED    = SHARED;
        bins BIN_SU0_EXCLUSIVE = EXCLUSIVE;
        bins BIN_SU0_MODIFIED  = MODIFIED;            
	} 

	MESI_SR0_TRANS: coverpoint c_mesi_snoop0 iff (vi_sbus_if.bus_rdx || vi_sbus_if.bus_rd){
	bins TRANS1_SR_A = (MODIFIED => SHARED) iff (u_mesi_snoop0 == SHARED);
	bins TRANS2_SR_A = (MODIFIED => INVALID) iff (u_mesi_snoop0 == INVALID); 
	bins TRANS3_SR_A = (EXCLUSIVE => SHARED) iff (u_mesi_snoop0 == SHARED);
	bins TRANS4_SR_A = (EXCLUSIVE => INVALID) iff (u_mesi_snoop0 == INVALID); 
	bins TRANS5_SR_A = (SHARED => INVALID) iff (u_mesi_snoop0 == INVALID);
	}
	
	MESI_SI0_TRANS: coverpoint c_mesi_snoop0 iff (vi_sbus_if.invalidate){
	bins TRANS1_SI_A = (SHARED => INVALID) iff (u_mesi_snoop0 == INVALID);
	}
    endgroup

    covergroup cover_mesi_snoop1;
	option.per_instance = 1;
        option.name = "cover_mesi_s1";
	MESI_C1_S: coverpoint c_mesi_snoop1{
        bins BIN_SC1_INVALID   = INVALID;
        bins BIN_SC1_SHARED    = SHARED;
        bins BIN_SC1_EXCLUSIVE = EXCLUSIVE;
        bins BIN_SC1_MODIFIED  = MODIFIED;            
	} 
	MESI_U1_S: coverpoint u_mesi_snoop1{ 
        bins BIN_SU1_INVALID   = INVALID;
        bins BIN_SU1_SHARED    = SHARED;
        bins BIN_SU1_EXCLUSIVE = EXCLUSIVE;
        bins BIN_SU1_MODIFIED  = MODIFIED;            
	} 

	MESI_SR1_TRANS: coverpoint c_mesi_snoop1 iff (vi_sbus_if.bus_rdx || vi_sbus_if.bus_rd){
	bins TRANS1_SR_B = (MODIFIED => SHARED) iff (u_mesi_snoop1 == SHARED);
	bins TRANS2_SR_B = (MODIFIED => INVALID) iff (u_mesi_snoop1 == INVALID); 
	bins TRANS3_SR_B = (EXCLUSIVE => SHARED) iff (u_mesi_snoop1 == SHARED);
	bins TRANS4_SR_B = (EXCLUSIVE => INVALID) iff (u_mesi_snoop1 == INVALID); 
	bins TRANS5_SR_B = (SHARED => INVALID) iff (u_mesi_snoop1 == INVALID);
	}
	
	MESI_SI1_TRANS: coverpoint c_mesi_snoop1 iff (vi_sbus_if.invalidate){
	bins TRANS1_SI_B = (SHARED => INVALID) iff (u_mesi_snoop1 == INVALID);
	}
    endgroup

    covergroup cover_mesi_snoop2;
	option.per_instance = 1;
        option.name = "cover_mesi_s2";
	MESI_C2_S: coverpoint c_mesi_snoop2{
        bins BIN_SC2_INVALID   = INVALID;
        bins BIN_SC2_SHARED    = SHARED;
        bins BIN_SC2_EXCLUSIVE = EXCLUSIVE;
        bins BIN_SC2_MODIFIED  = MODIFIED;            
	} 
	MESI_U2_S: coverpoint u_mesi_snoop2{ 
        bins BIN_SU2_INVALID   = INVALID;
        bins BIN_SU2_SHARED    = SHARED;
        bins BIN_SU2_EXCLUSIVE = EXCLUSIVE;
        bins BIN_SU2_MODIFIED  = MODIFIED;            
	} 

	MESI_SR2_TRANS: coverpoint c_mesi_snoop2 iff (vi_sbus_if.bus_rdx || vi_sbus_if.bus_rd){
	bins TRANS1_SR_C = (MODIFIED => SHARED) iff (u_mesi_snoop2 == SHARED);
	bins TRANS2_SR_C = (MODIFIED => INVALID) iff (u_mesi_snoop2 == INVALID); 
	bins TRANS3_SR_C = (EXCLUSIVE => SHARED) iff (u_mesi_snoop2 == SHARED);
	bins TRANS4_SR_C = (EXCLUSIVE => INVALID) iff (u_mesi_snoop2 == INVALID); 
	bins TRANS5_SR_C = (SHARED => INVALID) iff (u_mesi_snoop2 == INVALID);
	}
	
	MESI_SI2_TRANS: coverpoint c_mesi_snoop2 iff (vi_sbus_if.invalidate){
	bins TRANS1_SI_C = (SHARED => INVALID) iff (u_mesi_snoop2 == INVALID);
	}
    endgroup

    covergroup cover_mesi_snoop3;
	option.per_instance = 1;
        option.name = "cover_mesi_s3";
	MESI_C3_S: coverpoint c_mesi_snoop3{
        bins BIN_SC3_INVALID   = INVALID;
        bins BIN_SC3_SHARED    = SHARED;
        bins BIN_SC3_EXCLUSIVE = EXCLUSIVE;
        bins BIN_SC3_MODIFIED  = MODIFIED;            
	} 
	MESI_U3_S: coverpoint u_mesi_snoop3{ 
        bins BIN_SU3_INVALID   = INVALID;
        bins BIN_SU3_SHARED    = SHARED;
        bins BIN_SU3_EXCLUSIVE = EXCLUSIVE;
        bins BIN_SU3_MODIFIED  = MODIFIED;            
	} 

	MESI_SR3_TRANS: coverpoint c_mesi_snoop3 iff (vi_sbus_if.bus_rdx || vi_sbus_if.bus_rd){
	bins TRANS1_SR_D = (MODIFIED => SHARED) iff (u_mesi_snoop3 == SHARED);
	bins TRANS2_SR_D = (MODIFIED => INVALID) iff (u_mesi_snoop3 == INVALID); 
	bins TRANS3_SR_D = (EXCLUSIVE => SHARED) iff (u_mesi_snoop3 == SHARED);
	bins TRANS4_SR_D = (EXCLUSIVE => INVALID) iff (u_mesi_snoop3 == INVALID); 
	bins TRANS5_SR_D = (SHARED => INVALID) iff (u_mesi_snoop3 == INVALID);
	}
	
	MESI_SI3_TRANS: coverpoint c_mesi_snoop3 iff (vi_sbus_if.invalidate){
	bins TRANS1_SI_D = (SHARED => INVALID) iff (u_mesi_snoop3 == INVALID);
	}
    endgroup
    // Virtual interface of used to observe system bus interface signals
    virtual interface system_bus_interface vi_sbus_if;
    virtual interface cpu_mesi_lru_interface mesi_state_if0;
    virtual interface cpu_mesi_lru_interface mesi_state_if1;
    virtual interface cpu_mesi_lru_interface mesi_state_if2;
    virtual interface cpu_mesi_lru_interface mesi_state_if3;

    //constructor
    function new (string name, uvm_component parent);
        super.new(name, parent);
        sbus_out = new("sbus_out", this);
        this.cover_sbus_packet = new();
        this.cover_mesi_snoop0 = new();
        this.cover_mesi_snoop1 = new();
        this.cover_mesi_snoop2 = new();
        this.cover_mesi_snoop3 = new();
    endfunction : new

    //UVM build phase ()
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        // throw error if virtual interface is not set
        if (!uvm_config_db#(virtual system_bus_interface)::get(this, "","v_sbus_if", vi_sbus_if))
            `uvm_fatal("NO_VIF",{"virtual interface must be set for: ",get_full_name(),".vi_sbus_if"})
        if (!uvm_config_db#(virtual cpu_mesi_lru_interface)::get(this, "","mesi_if0", mesi_state_if0))
            `uvm_fatal("NO_VIF",{"virtual interface must be set for: ",get_full_name(),".mesi0_if"})
        if (!uvm_config_db#(virtual cpu_mesi_lru_interface)::get(this, "","mesi_if1", mesi_state_if1))
            `uvm_fatal("NO_VIF",{"virtual interface must be set for: ",get_full_name(),".mesi1_if"})
        if (!uvm_config_db#(virtual cpu_mesi_lru_interface)::get(this, "","mesi_if2", mesi_state_if2))
            `uvm_fatal("NO_VIF",{"virtual interface must be set for: ",get_full_name(),".mesi2_if"})
        if (!uvm_config_db#(virtual cpu_mesi_lru_interface)::get(this, "","mesi_if3", mesi_state_if3))
            `uvm_fatal("NO_VIF",{"virtual interface must be set for: ",get_full_name(),".mesi3_if"})
    endfunction: build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "RUN Phase", UVM_LOW)
        forever begin
        //TODO: Code for the system bus monitor is minimal!
        //Add code to observe other cases
        //Add code for dirty block eviction
        //Snoop requests, service time, etc
        
	    // trigger point for creating the packet
            @(posedge (|vi_sbus_if.bus_lv1_lv2_gnt_proc));
            `uvm_info(get_type_name(), "Packet creation triggered", UVM_LOW)
            s_packet = sbus_packet_c::type_id::create("s_packet", this);

            // wait for assertion of either bus_rd, bus_rdx or invalidate before monitoring other bus activities
            // lv2_rd for I-cache cases
            @(posedge(vi_sbus_if.bus_rd | vi_sbus_if.bus_rdx | vi_sbus_if.invalidate | vi_sbus_if.lv2_rd | vi_sbus_if.lv2_wr));

			if (vi_sbus_if.lv2_wr)
			begin
			s_packet.proc_evict_dirty_blk_flag = 1;
			s_packet.proc_evict_dirty_blk_data = vi_sbus_if.data_bus_lv1_lv2;
			s_packet.proc_evict_dirty_blk_addr = vi_sbus_if.addr_bus_lv1_lv2;
			end
			
            fork
                begin: cp_in_cache_check
                    // check for cp_in_cache assertion
                    @(posedge vi_sbus_if.cp_in_cache) s_packet.cp_in_cache = 1;
                end : cp_in_cache_check
                begin: shared_check
                    // check for shared signal assertion when data_in_bus_lv1_lv2 is also high
                    wait(vi_sbus_if.shared & vi_sbus_if.data_in_bus_lv1_lv2) s_packet.shared = 1;
                end : shared_check
		
		// check for lv2_wr assertion
                begin: snoop_wr_req_check
                    @(posedge vi_sbus_if.lv2_wr) s_packet.snoop_wr_req_flag = 1;
                end : snoop_wr_req_check

	    	begin: snoop_cover
			forever begin
				@(posedge mesi_state_if0.clk)
	     			if(vi_sbus_if.bus_rd | vi_sbus_if.bus_rdx | vi_sbus_if.invalidate)
	     			begin
	     				if(vi_sbus_if.bus_lv1_lv2_gnt_proc[0]!=1'b1)
	     				begin
	     				       c_mesi_snoop0 = mesi_state_if0.current_mesi_snoop;
	     				       u_mesi_snoop0 = mesi_state_if0.updated_mesi_snoop;
	     				       cover_mesi_snoop0.sample();
            				       //`uvm_info(get_type_name(), $sformatf("Mesi curr = %d, update = %d, proc = 0",c_mesi_snoop0,u_mesi_snoop0), UVM_LOW)
	     				end
	     				if(vi_sbus_if.bus_lv1_lv2_gnt_proc[1]!=1'b1)
	     				begin
	     				       c_mesi_snoop1 = mesi_state_if1.current_mesi_snoop;
	     				       u_mesi_snoop1 = mesi_state_if1.updated_mesi_snoop;
	     				       cover_mesi_snoop1.sample();
            				       //`uvm_info(get_type_name(), $sformatf("Mesi curr = %d, update = %d, proc = 1",c_mesi_snoop1,u_mesi_snoop1), UVM_LOW)
	     				end
	     				if(vi_sbus_if.bus_lv1_lv2_gnt_proc[2]!=1'b1)
	     				begin
	     				       c_mesi_snoop2 = mesi_state_if2.current_mesi_snoop;
	     				       u_mesi_snoop2 = mesi_state_if2.updated_mesi_snoop;
	     				       cover_mesi_snoop2.sample();
            				       //`uvm_info(get_type_name(), $sformatf("Mesi curr = %d, update = %d, proc = 2",c_mesi_snoop2,u_mesi_snoop2), UVM_LOW)
	     				end
	     				if(vi_sbus_if.bus_lv1_lv2_gnt_proc[3]!=1'b1)
	     				begin
	     				       c_mesi_snoop3 = mesi_state_if3.current_mesi_snoop;
	     				       u_mesi_snoop3 = mesi_state_if3.updated_mesi_snoop;
	     				       cover_mesi_snoop3.sample();
	     				end

				end

			end
	    	end: snoop_cover
            join_none

            // bus request type
            if (vi_sbus_if.bus_rd === 1'b1 && vi_sbus_if.addr_bus_lv1_lv2 >= 32'h4000_0000)//Data stored in instruction level cache is not shared so no coherence protocol is needed.
                s_packet.bus_req_type = BUS_RD;
				
			if (vi_sbus_if.invalidate === 1'b1)
                s_packet.bus_req_type = INVALIDATE;
				
			// bus request type with intention to modify 
			if (vi_sbus_if.bus_rdx === 1'b1)
                s_packet.bus_req_type = BUS_RDX;
				
			if (vi_sbus_if.bus_rd !== 1'b1 && vi_sbus_if.lv2_rd === 1'b1 && vi_sbus_if.addr_bus_lv1_lv2 < 32'h4000_0000)
				s_packet.bus_req_type = ICACHE_RD;

            // proc which requested the bus access
            case (1'b1)
                vi_sbus_if.bus_lv1_lv2_gnt_proc[0]: s_packet.bus_req_proc_num = REQ_PROC0;
                vi_sbus_if.bus_lv1_lv2_gnt_proc[1]: s_packet.bus_req_proc_num = REQ_PROC1;
                vi_sbus_if.bus_lv1_lv2_gnt_proc[2]: s_packet.bus_req_proc_num = REQ_PROC2;
                vi_sbus_if.bus_lv1_lv2_gnt_proc[3]: s_packet.bus_req_proc_num = REQ_PROC3;
            endcase

            // address requested
           s_packet.req_address = vi_sbus_if.addr_bus_lv1_lv2;

            // fork and call tasks
            fork: update_info
				begin
					@(|vi_sbus_if.bus_lv1_lv2_req_snoop)// check if any of the cpu is requesting a snoop 
					s_packet.bus_req_snoop = vi_sbus_if.bus_lv1_lv2_req_snoop;
				end
				begin
					@(vi_sbus_if.cp_in_cache)
					wait(vi_sbus_if.lv2_wr_done)
					s_packet.snoop_wr_req_flag = 1'b1;
					s_packet.wr_data_snoop = vi_sbus_if.data_bus_lv1_lv2;
				end
                // to determine which of snoops or L2 serviced read miss
                begin: req_service_check
                    if (s_packet.bus_req_type == BUS_RD)
                    begin
                        @(posedge vi_sbus_if.data_in_bus_lv1_lv2);
                        `uvm_info(get_type_name(), "Bus read successful", UVM_LOW)
                        s_packet.rd_data = vi_sbus_if.data_bus_lv1_lv2;
                        // check which had grant asserted
                        case (1'b1)
                            vi_sbus_if.bus_lv1_lv2_gnt_snoop[0]: s_packet.req_serviced_by = SERV_SNOOP0;
                            vi_sbus_if.bus_lv1_lv2_gnt_snoop[1]: s_packet.req_serviced_by = SERV_SNOOP1;
                            vi_sbus_if.bus_lv1_lv2_gnt_snoop[2]: s_packet.req_serviced_by = SERV_SNOOP2;
                            vi_sbus_if.bus_lv1_lv2_gnt_snoop[3]: s_packet.req_serviced_by = SERV_SNOOP3;
                            vi_sbus_if.bus_lv1_lv2_gnt_lv2     : s_packet.req_serviced_by = SERV_L2;
                        endcase
					
                    end
                end: req_service_check
				
				begin: ICACHE_req_service_check // to determine if L2 serviced Icache read miss
					if (s_packet.bus_req_type == ICACHE_RD)
					begin
						@(posedge vi_sbus_if.data_in_bus_lv1_lv2);
						`uvm_info(get_type_name(), "ICACHE_RD successful", UVM_LOW)
						s_packet.rd_data = vi_sbus_if.data_bus_lv1_lv2;
						// check which had grant asserted
						case (1'b1)
						vi_sbus_if.bus_lv1_lv2_gnt_snoop[0]: s_packet.req_serviced_by = SERV_SNOOP0;
						vi_sbus_if.bus_lv1_lv2_gnt_snoop[1]: s_packet.req_serviced_by = SERV_SNOOP1;
						vi_sbus_if.bus_lv1_lv2_gnt_snoop[2]: s_packet.req_serviced_by = SERV_SNOOP2;
						vi_sbus_if.bus_lv1_lv2_gnt_snoop[3]: s_packet.req_serviced_by = SERV_SNOOP3;
						vi_sbus_if.bus_lv1_lv2_gnt_lv2     : s_packet.req_serviced_by = SERV_L2;
						endcase
					end
				end: ICACHE_req_service_check
				
				begin: CHECK_INVALIDATE
					if (s_packet.bus_req_type == INVALIDATE)
					begin
						@(posedge vi_sbus_if.all_invalidation_done);
						`uvm_info(get_type_name(), "INVALIDATE successful", UVM_LOW)
					end
				end: CHECK_INVALIDATE
				
				begin :READ_MODIFY
				   if(s_packet.bus_req_type == BUS_RDX)
				   begin
					@(posedge vi_sbus_if.clk);
                      			@(posedge vi_sbus_if.clk); // wait for sufficient cycles for the snoop to identify 
				     	@(posedge vi_sbus_if.data_in_bus_lv1_lv2);// read the data 
					`uvm_info(get_type_name(), "BUS_RDX successful", UVM_LOW)
				     	s_packet.rd_data = vi_sbus_if.data_bus_lv1_lv2;
				     case (1'b1)
				        vi_sbus_if.bus_lv1_lv2_gnt_snoop[0]: s_packet.req_serviced_by = SERV_SNOOP0;
					vi_sbus_if.bus_lv1_lv2_gnt_snoop[1]: s_packet.req_serviced_by = SERV_SNOOP1;
					vi_sbus_if.bus_lv1_lv2_gnt_snoop[2]: s_packet.req_serviced_by = SERV_SNOOP2;
					vi_sbus_if.bus_lv1_lv2_gnt_snoop[3]: s_packet.req_serviced_by = SERV_SNOOP3;
					vi_sbus_if.bus_lv1_lv2_gnt_lv2     : s_packet.req_serviced_by = SERV_L2;
				     endcase
				   end
				end: READ_MODIFY
				
				

            join_none : update_info

            // wait until request is processed and send data
            @(negedge vi_sbus_if.bus_lv1_lv2_req_proc[0] or negedge vi_sbus_if.bus_lv1_lv2_req_proc[1] or negedge vi_sbus_if.bus_lv1_lv2_req_proc[2] or negedge vi_sbus_if.bus_lv1_lv2_req_proc[3]);
			 begin
			 s_packet.req_address = vi_sbus_if.addr_bus_lv1_lv2;
			if (vi_sbus_if.bus_rd === 1'b1 && vi_sbus_if.addr_bus_lv1_lv2 >= 32'h4000_0000)//Data stored in instruction level cache is not shared so no coherence protocol is needed.
                s_packet.bus_req_type = BUS_RD;
				
			if (vi_sbus_if.invalidate === 1'b1)
                s_packet.bus_req_type = INVALIDATE;
				
			// bus request type with intention to modify 
			if (vi_sbus_if.bus_rdx === 1'b1)
                s_packet.bus_req_type = BUS_RDX;
				
			if (vi_sbus_if.bus_rd !== 1'b1 && vi_sbus_if.lv2_rd === 1'b1 && vi_sbus_if.addr_bus_lv1_lv2 < 32'h4000_0000)
				s_packet.bus_req_type = ICACHE_RD;

            `uvm_info(get_type_name(), "Packet to be written", UVM_LOW)
			end
            // disable all spawned child processes from fork
            disable fork;

            // write into scoreboard after population of the packet fields
            sbus_out.write(s_packet);
            cover_sbus_packet.sample();
        end
    endtask : run_phase

endclass : system_bus_monitor_c
