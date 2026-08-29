// §33.5.3's separate compilation flow, which takes two invocations of
// deltahdl. The first compiles this source description into the library
// `cells` and writes the compiled form to cells.lib, because "it is essential
// that library cells persist, and the compiled forms shall, therefore, exist
// somewhere in the filesystem". The second is given cells.lib and the name of
// the configuration below and nothing else, which is §33.5.4's strategy: "the
// tool that actually does the binding only needs to be given the lib.cell
// specification for the top-level cell(s) and/or the config to be used. In
// this strategy, the config itself shall also be precompiled."
//
// separate_compilation_bind.before names the first invocation and
// separate_compilation_bind.args names the second. Both run in a temporary
// directory the runner makes, so cells.lib is written and read there and never
// beside this file.
//
// separate_compilation_top instantiates separate_compilation_leaf so that the
// bind has a hierarchy to descend. SeparateCompilationBinder::BindConfig in
// src/elaborator/separate_compilation_bind.cpp reads the subinstances of a
// cell out of that cell's compiled form and reports every name no loaded
// library holds a cell for, so a bind that read the top cell and descended no
// further would print `0 children` where the expected file holds `1 children`.
//
// The design statement writes the library `cells` in front of the top cell, so
// the cell has to be the one that library holds: FindDesignCell in
// src/elaborator/elaborator_resolve.cpp confines a design cell the source
// qualified to the named library, and `cells` is the name the first invocation
// passes to --precompile-into.
//
// Every byte of separate_compilation_bind.expected was derived by reading the
// sources rather than by running the tool. DumpIr in src/main.cpp writes
// `=== RTLIR Dump ===` and then one line per top module, and the six counts on
// that line are the sizes of RtlirModule::ports, ::nets, ::variables,
// ::assigns, ::processes and ::children in src/elaborator/rtlir.h.
// separate_compilation_top declares no port, no net, no variable, no
// continuous assignment and no process, and its one instantiation is the one
// child.
//
// PrecompiledLibrary::Load in src/parser/precompiled_library.cpp reads a
// compiled form back with the lexer and the parser alone, so this file carries
// no compiler directive: nothing here needs the preprocessor a bind never
// runs.
module separate_compilation_top;
  separate_compilation_leaf u();
endmodule

module separate_compilation_leaf;
endmodule

config separate_compilation_cfg;
  design cells.separate_compilation_top;
endconfig
