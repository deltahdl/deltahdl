// IEEE 1800-2023 §33.3.1 (printed page 935): a tool reads a predefined library
// map file before any source where the invocation names none, and deltahdl's
// is lib.map in the working directory. library_map_predefined.files puts one
// there, mapping adder.v into rtlLib and adder.vg into gateLib, with those two
// sources, which library_map_predefined.args names; no map file is named. This
// file matches neither specification, so its cells are compiled into work, and
// the configuration lists gateLib ahead of rtlLib, so a1 binds gateLib.adder
// and %l names it. Without the map read, both adders would go into work.
module library_map_predefined;
  adder a1();
endmodule

config library_map_predefined_cfg;
  design work.library_map_predefined;
  default liblist gateLib rtlLib;
endconfig
