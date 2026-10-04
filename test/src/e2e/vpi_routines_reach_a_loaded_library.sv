// §36.6 (printed page 987) makes a PLI application's C functions part of the
// tool, and Annexes K.1 and M.1 (printed pages 1306, 1326) and I have the tool
// provide the routines vpi_user.h, sv_vpi_user.h and svdpi.h declare. The
// library vpi_routines_reach_a_loaded_library.c, built beside the run and
// named by vpi_routines_reach_a_loaded_library.args, reports as deltahdl loads
// it whether it finds four of the VPI routines and two of svdpi.h's.
module t;
  initial $display("sv %0d", 1);
endmodule
