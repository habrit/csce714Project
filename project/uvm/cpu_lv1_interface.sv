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

//ASSERTION2: Address should not be invalid when rd/wr is processed. 
    property valid_addr_wr_rd;
        @(posedge clk)
          (cpu_rd || cpu_wr) |-> (addr_bus_cpu_lv1[31:0] !== 32'bx);
    endproperty

    assert_valid_addr_wr_rd: assert property (valid_addr_wr_rd)
    else 
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion assert_valid_addr_wr_rd Failed: Address is invalid when rd/wr is processed"))

//ASSERTION3: cpu_rd should be followed by data_in_bus_cpu_lv1 and both should be deasserted according to the HAS document. 
    property valid_rd_transaction;
        @(posedge clk)
            cpu_rd |=> ##[0:$] data_in_bus_cpu_lv1 ##1 !cpu_rd ##1 !data_in_bus_cpu_lv1;
    endproperty

    assert_valid_rd_transaction: assert property (valid_rd_transaction)
    else 
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion assert_valid_rd_transaction Failed: cpu_rd should be followed by data_in_bus_cpu_lv1 and both should be deasserted according to the HAS document"))

//ASSERTION4: If data_in_bus_cpu_lv1 is asserted, cpu_rd should be high
    property valid_data_in_bus_cpu_lv1;
        @(posedge clk)
            $rose(data_in_bus_cpu_lv1) |-> cpu_rd;
    endproperty

    assert_valid_data_in_bus_cpu_lv1: assert property (valid_data_in_bus_cpu_lv1)
    else 
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion assert_valid_data_in_bus_cpu_lv1 Failed: If data_in_bus_cpu_lv1 is asserted, cpu_rd should be high"))

// ASSERTION5: check valid address

// ASSERTION6: check data validity on write
    property prop_present_wr_data;
        @(posedge clk)
        (cpu_wr) |-> (data_in_bus_cpu_lv1);
    endproperty

    assert_present_wr_data: assert property (prop_present_wr_data)
    else
       `uvm_error("cpu_lv1_interface", $sformatf("Assertion assert_present_wr_data Failed: Write data not provided by CPU"));

// ASSERTION7: check data validity on read
    property prop_valid_rd_data;
        @(posedge clk)
        (cpu_rd) |-> (data_bus_cpu_lv1 !== 'z);
    endproperty

    assert_valid_rd_data: assert property (prop_valid_rd_data)
    else
        `uvm_error("cpu_lv1_interface", $sformatf("Assertion assert_valid_rd_data Failed: Read data not available on CPU-LV1 interface"));

// ASSERTION8: write acknowledgement
    property prop_wr_completion;
        @(posedge clk)
        (cpu_wr) |-> (cpu_wr_done);
    endproperty

    assert_wr_completion: assert property (prop_wr_completion)
    else
        `uvm_error("cpu_lv1_interface", $sformatf("Assertion assert_wr_completion Failed: Write operation not completed by LV1 cache"));



endinterface
