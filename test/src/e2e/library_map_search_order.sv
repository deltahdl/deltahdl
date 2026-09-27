// IEEE 1800-2023 §33.8.1: the -L arguments library_map_search_order.args names
// put gateLib ahead of rtlLib, overriding the declaration order of
// library_map/lib.map, which maps library_map/adder.v into rtlLib and
// library_map/adder.vg into gateLib. Both describe adder, so a1 binds
// gateLib.adder, and %l names it.
module library_map_search_order;
  adder a1();
endmodule
