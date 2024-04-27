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

//ASSERTION1: lv2_wr_done should not be asserted without lv2_wr being asserted in previous cycle
    assert_lv2_wr_done: assert property (prop_sig1_before_sig2(lv2_wr,lv2_wr_done))
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion assert_lv2_wr_done Failed: lv2_wr not asserted before lv2_wr_done goes high"))

//ASSERTION2: data_in_bus_lv1_lv2 and cp_in_cache should not be asserted without lv2_rd being asserted in previous cycle

assert_data_in_bus_lv1_lv2: assert property (prop_sig1_before_sig2(lv2_rd,data_in_bus_lv1_lv2))
	else
	`uvm_error("system_bus_interface",$sformatf("Assertion assert_data_in_bus_lv1_lv2 Failed: lv2_rd not asserted before data_in_bus_lv1_lv2 goes high"))


//TODO: Add assertions at this interface
//There are atleast 20 such assertions. Add as many as you can!!

//ASSERTION3: bus_rd should not be asserted without bus_rdx being asserted in previous cycle
	assert_bus_rd: assert property (prop_sig1_before_sig2(bus_rdx,bus_rd))
	else
	`uvm_error("system_bus_interface",$sformatf("Assertion assert_bus_rd Failed: bus_rdx not asserted before bus_rd goes high"))

// ASSERTION4: lv2_wr_done should not be asserted without lv2_wr being asserted in the same cycle
    assert_wr_done_without_wr: assert property (@(posedge clk)  !lv2_wr_done || lv2_wr)
    else
        `uvm_error("system_bus_interface", $sformatf("Assertion assert_wr_done_without_wr Failed: lv2_wr_done asserted without lv2_wr in the same cycle"))

// ASSERTION5: lv2_wr should not be high with lv2_rd
   assert_no_simultaneous_wr_rd: assert property (@(posedge clk)  !lv2_wr || !lv2_rd)
   else
       `uvm_error("system_bus_interface", $sformatf("Assertion assert_no_simultaneous_wr_rd Failed: lv2_wr should not be asserted with lv2_rd"))

// ASSERTION6: lv2_wr_done should not remain asserted for more than one cycle after lv2_wr is deasserted
    assert_wr_done_stays_high: assert property (@(posedge clk) !lv2_wr || lv2_wr_done)
    else
        `uvm_error("system_bus_interface", $sformatf("Assertion assert_wr_done_stays_high Failed: lv2_wr_done remains asserted after lv2_wr is deasserted"))

// ASSERTION7: lv2_rd should not be asserted without a valid address on addr_bus_lv1_lv2
    assert_rd_without_addr: assert property (@(posedge clk) !lv2_rd || ($countones(addr_bus_lv1_lv2) > 0))
    else
        `uvm_error("system_bus_interface",$sformatf("Assertion assert_rd_without_addr Failed: lv2_rd asserted without a valid address on addr_bus_lv1_lv2"))

// ASSERTION8: If lv2_rd is asserted, data_in_bus_lv1_lv2 should also be asserted
    assert_data_on_rd: assert property (@(posedge clk) !lv2_rd || data_in_bus_lv1_lv2)
    else
        `uvm_error("system_bus_interface", $sformatf("Assertion assert_data_on_rd Failed: lv2_rd asserted without data_in_bus_lv1_lv2"))

// ASSERTION9: shared should not be asserted without invalidate
    assert_shared_without_invalidate: assert property (@(posedge clk) !shared || invalidate)
    else
        `uvm_error("system_bus_interface", $sformatf("Assertion assert_shared_without_invalidate Failed: shared asserted without invalidate"))

// ASSERTION10: If lv2_rd is asserted, bus_lv1_lv2_gnt_snoop should be asserted for at least one core
    assert_rd_gnt_asserted: assert property (@(posedge clk) !lv2_rd || ($countones(bus_lv1_lv2_gnt_snoop) > 0))
    else
        `uvm_error("system_bus_interface", $sformatf("Assertion assert_rd_gnt_asserted Failed: lv2_rd asserted without bus_lv1_lv2_gnt_snoop"))

// ASSERTION11: All cores should eventually release bus access after being granted
    assert_release_after_gnt: assert property (@(posedge clk) ($countones(bus_lv1_lv2_gnt_proc) + $countones(bus_lv1_lv2_gnt_snoop)) == 0)
    else
        `uvm_error("system_bus_interface", $sformatf("Assertion assert_release_after_gnt Failed: Some cores did not release bus access after being granted"))

// ASSERTION12: No more than one core should be granted bus access at a time
    assert_single_core_access: assert property (@(posedge clk) ($countones(bus_lv1_lv2_gnt_proc) + $countones(bus_lv1_lv2_gnt_snoop)) <= 1)
    else
        `uvm_error("system_bus_interface", $sformatf("Assertion assert_single_core_access Failed: More than one core granted bus access at the same time"))


endinterface
