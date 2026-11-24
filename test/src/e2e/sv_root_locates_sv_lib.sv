module t;
  import "DPI-C" function int sv_root_locates_sv_lib_call(input int a);
  initial $display("r=%0d", sv_root_locates_sv_lib_call(7));
endmodule
