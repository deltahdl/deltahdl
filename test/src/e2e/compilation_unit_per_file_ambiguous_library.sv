// IEEE 1800-2023 §33.3.1.1 where each file is a compilation unit of its own
// (§3.12.1): library_map/ambiguous.map gives library_map/ambiguous.v to lib_a
// and to lib_b, each by its explicit file name, so the unit that file makes up
// maps to no one library, and the run is refused as it is where every file is
// one unit.
module compilation_unit_per_file_ambiguous_library;
  ambiguous_leaf u();
endmodule
