module library_map_default_liblist;
  adder a1();
endmodule

config library_map_default_liblist_cfg;
  design work.library_map_default_liblist;
  default liblist gateLib rtlLib;
endconfig
