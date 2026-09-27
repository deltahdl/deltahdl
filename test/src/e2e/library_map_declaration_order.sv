// IEEE 1800-2023 §33.3.1 (printed page 935): "all compliant tools shall
// provide a mechanism to specify one or more library map files to be used for
// a particular invocation of the tool". A command-line file ending in .map is
// one; library_map_declaration_order.args names library_map/lib.map, which maps
// library_map/adder.v into rtlLib and library_map/adder.vg into gateLib, and
// both describe adder. This file matches neither specification, so its top is
// compiled into work.
//
// §33.6.1 (printed page 945): "With no configuration, the libraries are
// searched according to the library declaration order in the library map
// file", so a1 binds rtlLib.adder, the library declared first, and %l names
// it.
module library_map_declaration_order;
  adder a1();
endmodule
