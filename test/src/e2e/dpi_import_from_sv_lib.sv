module t;
  import "DPI-C" function int dpi_import_from_sv_lib_call(input int a);
  initial $display("r=%0d", dpi_import_from_sv_lib_call(7));
endmodule
