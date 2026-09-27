// §33.5.4 (printed page 944): "the tool that actually does the binding only
// needs to be given the lib.cell specification for the top-level cell(s)
// and/or the config to be used". The design so bound is the design of the
// invocation, and running it is what shows which cell was bound.
//
// separate_compilation_bind_runs.before compiles this file into the library
// `runs` and writes it to runs.lib; separate_compilation_bind_runs.args loads
// runs.lib and names the configuration below. The bind elaborated the design
// and stopped, so the leaf's $display never ran and the invocation printed
// nothing. Both invocations run in a temporary directory the runner makes.
//
// PrecompiledLibrary::Load in src/parser/precompiled_library.cpp reads a
// compiled form back with the lexer and the parser alone, so this file carries
// no compiler directive.
module separate_compilation_runs_top;
  separate_compilation_runs_leaf #(.W(4)) u();
endmodule

module separate_compilation_runs_leaf #(parameter W = 8);
  initial $display("bound leaf W=%0d", W);
endmodule

config separate_compilation_runs_cfg;
  design runs.separate_compilation_runs_top;
endconfig
