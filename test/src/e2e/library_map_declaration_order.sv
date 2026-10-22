// IEEE 1800-2023 §33.3.1 (printed page 935) requires every compliant tool to
// offer a way of naming the library map files, one or more, that a given run of
// the tool uses. A command-line file ending in .map is one;
// library_map_declaration_order.args names library_map/lib.map, which maps
// library_map/adder.v into rtlLib and library_map/adder.vg into gateLib, and
// both describe adder. This file matches neither specification, so its top is
// compiled into work.
//
// §33.6.1 (printed page 945): where no configuration is in force, the libraries
// are searched in the order the library map file declares them, so a1 binds
// rtlLib.adder, the library declared first, and %l names it.
module library_map_declaration_order;
  adder a1();
endmodule
