//=====================================================================
// Project: 4 core MESI cache design
// File Name: cpu_mesi_lru_interface.sv
// Description: Basic CPU-LV1 interface with assertions
// Designers: Venky & Suru
//=====================================================================

interface cpu_mesi_lru_interface();

    import uvm_pkg::*;
    `include "uvm_macros.svh"


    parameter MESI_WID		     = `MESI_WID_LV1	   ; 
    parameter ASSOC_WID		     = `ASSOC_WID_LV1	   ; 
    parameter LRU_VAR_WID	     = `LRU_VAR_WID_LV1	   ; 

    logic [MESI_WID - 1 : 0]   	   current_mesi_snoop;
    logic [MESI_WID - 1 : 0]   	   updated_mesi_snoop;
    logic [MESI_WID - 1 : 0]   	   current_mesi_proc;
    logic [MESI_WID - 1 : 0]   	   updated_mesi_proc;

    logic			   clk;
    logic [1:0]			   proc_id;
    logic			   blk_hit_proc;
    logic			   blk_free;
    logic [LRU_VAR_WID - 1 : 0]    lru_var;
    logic [ASSOC_WID   - 1 : 0]    blk_accessed_main;
    logic [ASSOC_WID   - 1 : 0]    lru_replacement_proc;

endinterface
