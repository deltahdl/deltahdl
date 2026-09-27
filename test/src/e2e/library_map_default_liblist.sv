// IEEE 1800-2023 §33.6.2 (printed page 945): "The default liblist statement
// overrides the library search order in the lib.map file". The map
// library_map_default_liblist.args names declares rtlLib first, mapping
// library_map/adder.v into it and library_map/adder.vg into gateLib, and this
// file matches neither specification, so its cells are compiled into work.
// The configuration below lists gateLib ahead of rtlLib, so a1 binds
// gateLib.adder, and %l names it.
module library_map_default_liblist;
  adder a1();
endmodule

config library_map_default_liblist_cfg;
  design work.library_map_default_liblist;
  default liblist gateLib rtlLib;
endconfig
