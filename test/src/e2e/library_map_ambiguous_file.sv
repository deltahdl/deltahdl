// IEEE 1800-2023 §33.3.1.1: library_map/ambiguous.map, which
// library_map_ambiguous_file.args names, gives library_map/ambiguous.v to
// lib_a and to lib_b, each by its explicit file name, so neither claims it
// more specifically than the other and the file maps to no one library. The
// run is refused.
module library_map_ambiguous_file;
  ambiguous_leaf u();
endmodule
