module library_map_primitive_cell;
  wire y;
  reg a = 0;
  inv u(y, a);
  initial #1 $display("y=%b", y);
endmodule

config library_map_primitive_cell_cfg;
  design work.library_map_primitive_cell;
  default liblist rtlLib;
endconfig
