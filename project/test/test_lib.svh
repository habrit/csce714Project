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