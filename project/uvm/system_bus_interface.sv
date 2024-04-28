//=====================================================================
// Project: 4 core MESI cache design
// File Name: system_bus_interface.sv
// Description: Basic system bus interface including arbiter
// Designers: Venky & Suru
//=====================================================================

interface system_bus_interface(input clk);

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    parameter DATA_WID_LV1        = `DATA_WID_LV1       ;
    parameter ADDR_WID_LV1        = `ADDR_WID_LV1       ;
    parameter NO_OF_CORE            = 4;

    wire [DATA_WID_LV1 - 1 : 0] data_bus_lv1_lv2     ;
    wire [ADDR_WID_LV1 - 1 : 0] addr_bus_lv1_lv2     ;
    wire                        bus_rd               ;
    wire                        bus_rdx              ;
    wire                        lv2_rd               ;
    wire                        lv2_wr               ;
    wire                        lv2_wr_done          ;
    wire                        cp_in_cache          ;
    wire                        data_in_bus_lv1_lv2  ;

    wire                        shared               ;
    wire                        all_invalidation_done;
    wire                        invalidate           ;

    logic [NO_OF_CORE - 1  : 0]   bus_lv1_lv2_gnt_proc ;
    logic [NO_OF_CORE - 1  : 0]   bus_lv1_lv2_req_proc ;
    logic [NO_OF_CORE - 1  : 0]   bus_lv1_lv2_gnt_snoop;
    logic [NO_OF_CORE - 1  : 0]   bus_lv1_lv2_req_snoop;
    logic                       bus_lv1_lv2_gnt_lv2  ;
    logic                       bus_lv1_lv2_req_lv2  ;

//Assertions
//property that checks that signal_1 is asserted in the previous cycle of signal_2 assertion
    property prop_sig1_before_sig2(signal_1,signal_2);
    @(posedge clk)
        signal_2 |-> $past(signal_1);
    endproperty

//ASSERTION 1: lv2_wr_done should not be asserted without lv2_wr being asserted in previous cycle
    assert_lv2_wr_done: assert property (prop_sig1_before_sig2(lv2_wr,lv2_wr_done))
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion assert_lv2_wr_done Failed: lv2_wr not asserted before lv2_wr_done goes high"))


//ASSERTION 2: data_in_bus_lv1_lv2 and cp_in_cache should not be asserted without lv2_rd being asserted in previous cycle
assert_lv2_rd_data_in_bus_lv1_lv2 : assert property (prop_sig1_before_sig2(lv2_rd, data_in_bus_lv1_lv2))
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion assert_lv2_rd_data_in_bus_lv1_lv2 Failed: lv2_rd not asserted before data_in_bus_lv1_lv2 high"))

assert_lv2_rd_cp_in_cache : assert property (prop_sig1_before_sig2(lv2_rd, cp_in_cache))
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion assert_lv2_rd_cp_in_cache Failed: lv2_rd not asserted before cp_in_cache high"))


//TODO: Add assertions at this interface
//There are atleast 20 such assertions. Add as many as you can!!



//ASSERTION 3: Once access granted (bus_lv1_lv2_gnt_proc = 1), only then bus_rd and lv2_rd is raised/asserted.
assert_bus_rd_lv2_rd : assert property (prop_sig1_before_sig2(bus_lv1_lv2_gnt_proc, bus_rd && lv2_rd))
else 
   `uvm_error("system_bus_interface",$sformatf("Assertion assert_bus_rd_lv2_rd Failed : bus_rd and lv2_rd is asserted even before bus_lv1_lv2_gnt_proc"))

assert_bus_rdx_lv2_rd : assert property (prop_sig1_before_sig2(bus_lv1_lv2_gnt_proc, bus_rdx && lv2_rd))
else 
   `uvm_error("system_bus_interface",$sformatf("Assertion assert_bus_rdx_lv2_rd Failed : bus_rdx and lv2_rd is asserted even before bus_lv1_lv2_gnt_proc"))



//General Property Definition 
property prop_gnt_onehot(signal_one_hot); 
      @(posedge clk)
                $onehot0(signal_one_hot);
endproperty

// ASSERTION 4: The grant signal (for the proc side) is one hot. 
assert_lv1_gnt_proc_onehot : assert property (prop_gnt_onehot(bus_lv1_lv2_gnt_proc))
else 
    `uvm_error("system_bus_interface",$sformatf("Assertion assert_lv1_gnt_proc_onehot Failed: the bus_lv1_lv2_gnt_proc is not a onehot signal"))

//ASSERTION 5: The grant signal (for the snoop side) is one hot.
assert_lv1_gnt_snoop_onehot : assert property (prop_gnt_onehot(bus_lv1_lv2_gnt_snoop))
else 
    `uvm_error("system_bus_interface",$sformatf("Assertion assert_lv1_gnt_snoop_onehot Failed: the bus_lv1_lv2_gnt_snoop is not a onehot signal"))





//ASSERTION 6: snoop grants are assigned only if a proc grant has already been assigned
    property prop_proc_gnt_before_snoop_gnt;
    @(posedge clk)
        (|(bus_lv1_lv2_gnt_snoop) && !$past(|(bus_lv1_lv2_gnt_snoop))) |-> |(bus_lv1_lv2_gnt_proc);
    endproperty

    assert_proc_gnt_before_snoop_gnt: assert property (prop_proc_gnt_before_snoop_gnt)
    else
        `uvm_error("system_bus_interface",$sformatf("Assertion assert_proc_gnt_before_snoop_gnt Failed: snoop grant exists without a proc grant"))





// ASSERTION 7: After bus_lv1_lv2_gnt_snoop is asserted in a particular clock cycle, from the next clock cycle or in the later clock cycles, the signals 'shared' and 'data_in_bus_lv1_lv2' will be asserted at the same time. 
property prop_bus_gnt_snoop_shared;
@(posedge clk)
(|bus_lv1_lv2_gnt_snoop) |=> ##[0:$] (shared && data_in_bus_lv1_lv2);
endproperty

assert_bus_gnt_snoop_shared : assert property (prop_bus_gnt_snoop_shared)
else
  `uvm_error("system_bus_interface",$sformatf("Assertion assert_bus_gnt_snoop_shared Failed for core/proc: shared and data_in_bus_lv1_lv2 not asserted after the bus_lv1_lv2_gnt_snoop"))





// ASSERTION 8: Whenever bus_lv1_lv2_req_snoop is asserted , wait for data_in_bus_lv1_lv2 assert and bus_lv1_lv2_req_snoop is deasserted
property prop_bus_lv1_lv2_req_snoop;
@(posedge clk)
   $rose(|bus_lv1_lv2_req_snoop) |-> ##[1:$] data_in_bus_lv1_lv2 ##[1:$] $fell(|bus_lv1_lv2_req_snoop);
endproperty  

assert_bus_lv1_lv2_req_snoop: assert property (prop_bus_lv1_lv2_req_snoop)
else 
	`uvm_error("system_bus_interface",$sformatf("Assertion assert_bus_lv1_lv2_req_snoop Failed: bus_lv1_lv2_req_snoop is not de asserted properly"))





// invalidate is asserted - wait for all_invalidation_done to go high
//ASSERTION 9: whenever invalidate goes high, wait for all invalidation done signal to go high
property prop_invalidate;
@(posedge clk)
	invalidate |-> ##[0:$] all_invalidation_done;
endproperty

assert_invalidate : assert property (prop_invalidate)
else
	`uvm_error("system_bus_interface",$sformatf("Assertion assert_invalidate Failed: all_invalidation is not done properly"))





// When bus_lv1_lv2_gnt_proc eventually goes high, then  bus_lv1_lv2_req_proc goes low.
//ASSERTION 10: Processor request should be served - processor request is followed by corresponding grant assertion and request de assertion
property prop_bus_lv1_lv2_req_proc;
@(posedge clk)	 
   (|bus_lv1_lv2_gnt_proc) |-> ##[0:$] !(|bus_lv1_lv2_req_proc);
endproperty

assert_bus_lv1_lv2_req_proc : assert property (prop_bus_lv1_lv2_req_proc)
else
	`uvm_error("system_bus_interface",$sformatf("Assertion assert_prop_bus_lv1_lv2_req_proc Failed:Processor request is not served "))





// bus_rd and lv2_rd is raised - addr_bus_lv1_lv2
//ASSERTION 11: addr_bus_lv1_lv2 should be valid when bus_rd/lv2_rd request is asserted
property prop_addr_check_valid_lv2;
    @(posedge clk)
      (bus_rd && lv2_rd) |-> !($isunknown(^addr_bus_lv1_lv2));
endproperty

assert_valid_addr_check_lv2: assert property (prop_addr_check_valid_lv2)
else
	`uvm_error("system_bus_interface",$sformatf("Assertion assert_valid_addr_check_lv2 Failed: addr_bus_lv1_lv2 is not valid when bus_rd/lv2_rd is asserted"))






// On lv2rd, if cp_in_cache is high then - bus_lv1_lv2_req_lv2 is deasserted
//ASSERTION 13 : if cp_in_cache assert then bus_lv1_lv2_req_lv2 is deasserted immediately in the same cycle
property prop_cp_in_cache;
@(posedge clk)
	(lv2_rd && cp_in_cache) |=> !(bus_lv1_lv2_req_lv2);
endproperty

assert_prop_cp_in_cache : assert property (prop_cp_in_cache)
else
	`uvm_error("system_bus_interface",$sformatf("Assertion assert_cp_in_cache Failed: cp_in_cache is asserted  lv2_bus_req is not cancelled"))





//ASSERTION 14:
//property for lv2_wr 
property prop_lv2_wr_done_handshake_rise_fall;
        @(posedge clk)
          $rose(lv2_wr_done) |=> $fell(lv2_wr);
    endproperty

    assert_prop_lv2_wr_done_handshake_rise_fall: assert property (prop_lv2_wr_done_handshake_rise_fall)
    else
        `uvm_error("system_bus_interface",$sformatf("Assertion prop_lv2_wr_done_handshake_rise_fall Failed: lv2_wr and lv2_wr_done handshake failed"))





//ASSERTION 15: lv2_wr_done should be deasserted one cycle after lv2_wr is deasserted
//property for lv2_wr
property prop_lv2_wr_done_handshake_fall_fall;
        @(posedge clk)
          $fell(lv2_wr) |-> ##[0:1] $fell(lv2_wr_done);
    endproperty

    assert_prop_lv2_wr_done_handshake_fall_fall: assert property (prop_lv2_wr_done_handshake_fall_fall)
    else
        `uvm_error("system_bus_interface",$sformatf("Assertion prop_lv2_wr_done_handshake_fall_fall Failed: Falling edge of lv2_wr was not followed by falling edge of lv2_wr_done"))





//ASSERTION 16: On bus snoop request, if data_in_bus_lv1_lv2 is already high, the snoop request is immediately deasserted if the snoop request has not been granted till then
    property prop_snoop_req_imm_deassert(req,gnt);
    @(posedge clk)
        ((req && data_in_bus_lv1_lv2) && !gnt) |=> !req;
    endproperty

    assert_snoop_req_imm_deassert_c0: assert property(prop_snoop_req_imm_deassert(bus_lv1_lv2_req_snoop[0],bus_lv1_lv2_gnt_snoop[0]))
    else
        `uvm_error("system_bus_interface",$sformatf("Assertion assert_snoop_req_imm_deassert_c0 Failed: bus_lv1_lv2_req_snoop not deasserted when data_in_bus_lv1_lv2 is asserted without the corresponding gnt being asserted for Cache 0"))

    assert_snoop_req_imm_deassert_c1: assert property(prop_snoop_req_imm_deassert(bus_lv1_lv2_req_snoop[1],bus_lv1_lv2_gnt_snoop[1]))
    else
        `uvm_error("system_bus_interface",$sformatf("Assertion assert_snoop_req_imm_deassert_c0 Failed: bus_lv1_lv2_req_snoop not deasserted when data_in_bus_lv1_lv2 is asserted without the corresponding gnt being asserted for Cache 1"))

    assert_snoop_req_imm_deassert_c2: assert property(prop_snoop_req_imm_deassert(bus_lv1_lv2_req_snoop[2],bus_lv1_lv2_gnt_snoop[2]))
    else
        `uvm_error("system_bus_interface",$sformatf("Assertion assert_snoop_req_imm_deassert_c0 Failed: bus_lv1_lv2_req_snoop not deasserted when data_in_bus_lv1_lv2 is asserted without the corresponding gnt being asserted for Cache 2"))

    assert_snoop_req_imm_deassert_c3: assert property(prop_snoop_req_imm_deassert(bus_lv1_lv2_req_snoop[3],bus_lv1_lv2_gnt_snoop[3]))
    else
        `uvm_error("system_bus_interface",$sformatf("Assertion assert_snoop_req_imm_deassert_c0 Failed: bus_lv1_lv2_req_snoop not deasserted when data_in_bus_lv1_lv2 is asserted without the corresponding gnt being asserted for Cache 3"))





//ASSERTION 17: All bus gnt should be deasserted when their corresponding req are deasserted
    property prop_bus_gnt_deassert(req,gnt);
    @(posedge clk)
        $fell(req) |-> !gnt;
    endproperty

    //Proc side
    assert_bus_gnt_deassert_proc_c0: assert property(prop_bus_gnt_deassert(bus_lv1_lv2_req_proc[0],bus_lv1_lv2_gnt_proc[0]))
    else
        `uvm_error("system_bus_interface",$sformatf("Assertion assert_bus_gnt_deassert_proc_c0 Failed: bus_lv1_lv2_gnt_proc not deasserted when the corresponding req was deasserted for cache 0"))

    assert_bus_gnt_deassert_proc_c1: assert property(prop_bus_gnt_deassert(bus_lv1_lv2_req_proc[1],bus_lv1_lv2_gnt_proc[1]))
    else
        `uvm_error("system_bus_interface",$sformatf("Assertion assert_bus_gnt_deassert_proc_c1 Failed: bus_lv1_lv2_gnt_proc not deasserted when the corresponding req was deasserted for cache 1"))

    assert_bus_gnt_deassert_proc_c2: assert property(prop_bus_gnt_deassert(bus_lv1_lv2_req_proc[2],bus_lv1_lv2_gnt_proc[2]))
    else
        `uvm_error("system_bus_interface",$sformatf("Assertion assert_bus_gnt_deassert_proc_c2 Failed: bus_lv1_lv2_gnt_proc not deasserted when the corresponding req was deasserted for cache 2"))

    assert_bus_gnt_deassert_proc_c3: assert property(prop_bus_gnt_deassert(bus_lv1_lv2_req_proc[3],bus_lv1_lv2_gnt_proc[3]))
    else
        `uvm_error("system_bus_interface",$sformatf("Assertion assert_bus_gnt_deassert_proc_c3 Failed: bus_lv1_lv2_gnt_proc not deasserted when the corresponding req was deasserted for cache 3"))

    //Snoop side
    assert_bus_gnt_deassert_snoop_c0: assert property(prop_bus_gnt_deassert(bus_lv1_lv2_req_snoop[0],bus_lv1_lv2_gnt_snoop[0]))
    else
        `uvm_error("system_bus_interface",$sformatf("Assertion assert_bus_gnt_deassert_snoop_c0 Failed: bus_lv1_lv2_gnt_snoop not deasserted when the corresponding req was deasserted for cache 0"))

    assert_bus_gnt_deassert_snoop_c1: assert property(prop_bus_gnt_deassert(bus_lv1_lv2_req_snoop[1],bus_lv1_lv2_gnt_snoop[1]))
    else
        `uvm_error("system_bus_interface",$sformatf("Assertion assert_bus_gnt_deassert_snoop_c1 Failed: bus_lv1_lv2_gnt_snoop not deasserted when the corresponding req was deasserted for cache 1"))

    assert_bus_gnt_deassert_snoop_c2: assert property(prop_bus_gnt_deassert(bus_lv1_lv2_req_snoop[2],bus_lv1_lv2_gnt_snoop[2]))
    else
        `uvm_error("system_bus_interface",$sformatf("Assertion assert_bus_gnt_deassert_snoop_c2 Failed: bus_lv1_lv2_gnt_snoop not deasserted when the corresponding req was deasserted for cache 2"))

    assert_bus_gnt_deassert_snoop_c3: assert property(prop_bus_gnt_deassert(bus_lv1_lv2_req_snoop[3],bus_lv1_lv2_gnt_snoop[3]))
    else
        `uvm_error("system_bus_interface",$sformatf("Assertion assert_bus_gnt_deassert_snoop_c3 Failed: bus_lv1_lv2_gnt_snoop not deasserted when the corresponding req was deasserted for cache 3"))





//ASSERTION 18: 
//property for signal1 and signal2.
property prop_onehot (signal1, signal2);
@(posedge clk)
            (signal1 || signal2 ) |-> (!(signal1 && signal2) !== 0);
endproperty

assert_prop_bus_rd_bus_rdx: assert property (prop_onehot (bus_rd, bus_rdx))
else
    `uvm_error("system_bus_interface",$sformatf("Assertion assert_prop_bus_rd_bus_rdx failed: bus_rd and bus_rdx are asserted at the same time"))

assert_prop_bus_rd_invalidate: assert property (prop_onehot (bus_rd, invalidate))
else
    `uvm_error("system_bus_interface",$sformatf("Assertion assert_prop_bus_rd_invalidate failed: bus_rd and invalidate are asserted at the same time"))

assert_prop_bus_rdx_invalidate: assert property (prop_onehot (bus_rdx, invalidate))
else
    `uvm_error("system_bus_interface",$sformatf("Assertion assert_prop_bus_rdx_invalidate failed: bus_rdx and invalidate are asserted at the same time"))





//ASSERTION 19:
property prop_valid_address_range;
@(posedge clk)
       !($isunknown(addr_bus_lv1_lv2)) |-> (addr_bus_lv1_lv2 inside {[0:((1 <<ADDR_WID_LV1)-1)]});
       //(1 << ADDR_WID_LV1) == (1 << 32);
       //32'h5000_AAAC < (1 << ADDR_WID_LV1);
endproperty

assert_valid_address_range : assert property (prop_valid_address_range)
else 
     `uvm_error("system_bus_interface", $sformatf("Assertion assert_valid_address_range Failed: The address value/range is out of bounds"))





//ASSERTION 20:
property prop_bus_lv1_lv2_gnt_proc_invalidate;
@(posedge clk)
//(!(lv2_wr) && bus_lv1_lv2_gnt_proc) |=> !($isunknown(invalidate));
 invalidate |-> (|bus_lv1_lv2_gnt_proc);
endproperty

assert_bus_gnt_proc_invalidate : assert property (prop_bus_lv1_lv2_gnt_proc_invalidate)
else 
     `uvm_error("system_bus_interface", $sformatf("Assertion assert_bus_gnt_proc_invalidate Failed: invalidate signal is asserted without bus_lv1_lv2_gnt_proc"))



//ASSERTION 21: If bus_rd or bus_rdx asserted, then lv2_rd also asserted.
//property that checks if signal_1 is asserted when signal_2 is asserted
    property prop_sig2_with_sig1(signal_1, signal_2);
    @(posedge clk)
        signal_2 |-> signal_1;
    endproperty

    assert_bus_rd_rdx_with_lv2_rd: assert property (prop_sig2_with_sig1(lv2_rd,(bus_rd||bus_rdx)))
    else
        `uvm_error("system_bus_interface",$sformatf("Assertion assert_bus_rd_rdx_with_lv2_rd Failed: bus_rd/bus_rdx asserted without a lv2_rd"))





//ASSERTION 22: bus_rd, invalidate and bus_rdx cannot be simultaneously asserted
    property prop_simult_bus_rd_rdx;
    @(posedge clk)
        not(bus_rd && bus_rdx && invalidate);
    endproperty

    assert_simult_bus_rd_rdx: assert property(prop_simult_bus_rd_rdx)
    else
        `uvm_error("system_bus_interface",$sformatf("Assertion assert_simult_bus_rd_rdx Failed: bus_rd, invalidate and bus_rdx simultaneously asserted"))





//ASSERTION 23: When invalidate is high, there is atleast one cache req on bus
    property prop_invalidate_assert;
    @(posedge clk)
        invalidate |-> (|bus_lv1_lv2_gnt_proc);
    endproperty

    assert_invalidate_assert: assert property(prop_invalidate_assert)
    else
        `uvm_error("system_bus_interface",$sformatf("Assertion assert_invalidate_assert Failed: invalidate is asserted without any bus_lv1_lv2_gnt_proc"))


endinterface

