module t;
  import "DPI-C" function int sv_root_locates_bootstrap_call(input int a);
  initial $display("r=%0d", sv_root_locates_bootstrap_call(7));
endmodule
