module t;
  import "DPI-C" function int dpi_import_from_bootstrap_entry_call(input int a);
  initial $display("r=%0d", dpi_import_from_bootstrap_entry_call(7));
endmodule
