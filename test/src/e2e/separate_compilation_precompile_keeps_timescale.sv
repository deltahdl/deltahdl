// §33.5.3 (printed page 944) compiles source descriptions into a library, and
// a source description holds compiler directives (Clause 22) the compile reads
// as it reads the rest. §3.14.2.3 gives sc_ts_top the `timescale in force at
// its header, and §33.5.4 has the binding run read no source description, so
// the compile records that timescale beside the cell and the bind applies it:
// $printtimescale (§20.4.2) reports 1us / 1ns.
//
// separate_compilation_precompile_keeps_timescale.before compiles this file
// into ts.lib, which the precompile used to refuse at the grave accent;
// separate_compilation_precompile_keeps_timescale.args binds sc_ts_top from it.
`timescale 1us / 1ns
module sc_ts_top;
  initial $printtimescale;
endmodule
