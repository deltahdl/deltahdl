module library_map_predefined;
  adder a1();
endmodule

config library_map_predefined_cfg;
  design work.library_map_predefined;
  default liblist gateLib rtlLib;
endconfig
