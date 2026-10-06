// A.1.2 (printed page 1172) makes an empty source file valid source text that
// adds nothing to the design, so a precompile (§33.5.3) reads one as that and
// goes on to the sources after it.
//
// separate_compilation_precompile_empty_source.before compiles this file,
// empty.sv and after.sv into sc.lib, which the precompile used to stop at the
// empty file with status 1; separate_compilation_precompile_empty_source.args
// binds sc_empty_after_top from it, a cell of after.sv instantiating the leaf
// below, and it prints.
module sc_empty_leaf;
endmodule
