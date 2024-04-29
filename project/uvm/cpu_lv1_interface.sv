//=====================================================================
// Project: 4 core MESI cache design
// File Name: cpu_lv1_interface.sv
// Description: Basic CPU-LV1 interface with assertions
// Designers: Venky & Suru
//=====================================================================


interface cpu_lv1_interface(input clk);

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    parameter DATA_WID_LV1           = `DATA_WID_LV1       ;
    parameter ADDR_WID_LV1           = `ADDR_WID_LV1       ;
    parameter TIME_OUT               = 110;

    reg   [DATA_WID_LV1 - 1   : 0] data_bus_cpu_lv1_reg    ;

    wire  [DATA_WID_LV1 - 1   : 0] data_bus_cpu_lv1        ;
    logic [ADDR_WID_LV1 - 1   : 0] addr_bus_cpu_lv1        ;
    logic                          cpu_rd                  ;
    logic                          cpu_wr                  ;
    logic                          cpu_wr_done             ;
    logic                          data_in_bus_cpu_lv1     ;

    assign data_bus_cpu_lv1 = data_bus_cpu_lv1_reg ;

//Assertions
//ASSERTION1: cpu_wr and cpu_rd should not be asserted at the same clock cycle
    property prop_simult_cpu_wr_rd;
        @(posedge clk)
          not(cpu_rd && cpu_wr);
    endproperty

    assert_simult_cpu_wr_rd: assert property (prop_simult_cpu_wr_rd)
    else
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion assert_simult_cpu_wr_rd Failed: cpu_wr and cpu_rd asserted simultaneously"))

//TODO: Add assertions at this interface
//ASSERTION 2: Writes to Instruction Cache is Invalid. If write requests are asserted, then the address can never be less than 32'h 4000_0000.

property prop_write_instn_cache; 
     @(posedge clk)
         (cpu_wr == 1) |-> ((addr_bus_cpu_lv1 >= 32'h 4000_0000) && cpu_wr);  
endproperty 
assert_write_instn_cache : assert property (prop_write_instn_cache)
else
    `uvm_error("cpu_lv1_interface",$sformatf("Assertion assert_write_instn_cache Failed: An attempt to write into the instruction cache was done"))


//ASSERTION 3: write done signal should be deasserted 1 clock cycle after write signal is deasserted. 
property prop_write_deassert;
   @(posedge clk)
         $fell(cpu_wr) |-> ##[0:$] $fell(cpu_wr_done);
endproperty
assert_prop_write_deassert : assert property (prop_write_deassert) 
else
    `uvm_error("cpu_lv1_interface",$sformatf("Assertion assert_prop_write_deassert Failed: Write done signal is still asserted even after write signal is deasserted in the previous clock"))


//ASSERTION 4: Write signal should be deasserted after write to cache is completed. 
property prop_write_deassert_1;
  @(posedge clk)
     $rose(cpu_wr_done) |=> $fell(cpu_wr);
endproperty
assert_prop_write_deassert_1 : assert property (prop_write_deassert_1)
else
    `uvm_error("cpu_lv1_interface",$sformatf("Assertion assert_prop_write_deassert_1 Failed: Write signal continues to be asserted"))


//ASSERTION 5: data in bus should not have unknowns (X) while data_in_bus is asserted.
property prop_data_in_bus_is_real_data;
        @(posedge clk)
          $rose(data_in_bus_cpu_lv1) |->  (data_in_bus_cpu_lv1 == (^data_bus_cpu_lv1 !== 1'bx));
endproperty
assert_data_in_bus_is_real_data: assert property (prop_data_in_bus_is_real_data)
else
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion assert_data_in_bus_is_real_data Failed: data in bus has unknowns while data_in_bus asserted"))

/*
//ASSERTION 6: read level1 cache hit (cpu_rd should be followed by data_in_bus_cpu_lv1 assertion (next cycle to any number of cycles), and then both the signals should be deasserted in consecutive cycles)
    property prop_cpu_rd_data_in_bus_handshake;
        @(posedge clk)
          cpu_rd |-> ##[1:TIME_OUT] data_in_bus_cpu_lv1 ##1 (!cpu_rd) ##1 (!data_in_bus_cpu_lv1);
    endproperty

    assert_cpu_rd_data_in_bus_handshake: assert property (prop_cpu_rd_data_in_bus_handshake)
    else
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion assert_cpu_rd_data_in_bus_handshake Failed: cpu_rd and data_in_bus_cpu_lv1 handshake failed"))
*/

//ASSERTION 7: write level1 cache hit (when cpu_wr is asserted, valid data should be available in data_bus_cpu_lv1 (at the same cycle)).
    property prop_cpu_wr_data_bus_cpu_lv1;
        @(posedge clk)
          cpu_wr |-> (^data_bus_cpu_lv1 !== 1'bx);
    endproperty

    assert_cpu_wr_data_bus_cpu_lv1: assert property (prop_cpu_wr_data_bus_cpu_lv1)
    else
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion assert_cpu_wr_data_bus_cpu_lv1 Failed: When write request is asserted, data bus has insignificant data"))

//ASSERTION 8: addr_bus_cpu_lv1 should be valid when cpu_rd/cpu_wr request is asserted
    property prop_valid_addr_check;
        @(posedge clk)
          (cpu_rd||cpu_wr) |-> (^addr_bus_cpu_lv1 !== 1'bx);
    endproperty

    assert_valid_addr_check: assert property (prop_valid_addr_check)
    else
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion assert_valid_addr_check Failed: addr_bus_cpu_lv1 is not valid when cpu_rd/cpu_wr is asserted"))

/*
// ASSERTION9: write acknlwedgement time out
    property prop_wr_completion;
        @(posedge clk)
        (cpu_wr) |-> ##[0:100] (cpu_wr_done);
    endproperty

    assert_wr_completion: assert property (prop_wr_completion)
    else
        `uvm_error("cpu_lv1_interface", $sformatf("Assertion assert_wr_completion Failed: Write operation not completed by LV1 cache"));
*/



endinterface

