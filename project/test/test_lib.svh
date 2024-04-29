//=====================================================================
// Project: 4 core MESI cache design
// File Name: test_lib.svh
// Description: Base test class and list of tests
// Designers: Venky & Suru
//=====================================================================
//TODO: add your testcase files in here
`include "base_test.sv"
`include "read_miss_icache.sv"
`include "read_miss_icache5.sv"
`include "illegalwrite.sv"
`include "random_write.sv"
`include "write_miss.sv"
`include "write_miss_replacement_shared.sv"
`include "shared_to_invalid.sv"
`include "read_hit_dcache.sv"
`include "read_write_same_proc.sv"
`include "read_two_procs_force_write.sv"
`include "write_hit_lv2.sv"
`include "write_hit_dcache_ex.sv"
`include "write_hit_dcache_shared.sv"
`include "read_hit_lv2.sv"
`include "fsm_exclusive_to_others.sv"
`include "ex_to_shared.sv"
`include "ex_to_mod.sv"
`include "ex_to_invalid.sv"
`include "multi_proc_rd_wr_rd.sv"
`include "read_miss_cp_modified.sv"
`include "mesi_test.sv"
`include "write_miss_cp_cache.sv"
`include "write_miss_replacement.sv"