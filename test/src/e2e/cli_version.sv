// --version answers with deltahdl's name and version and exits 0 without
// reading the source named beside it, which is never compiled: the module here
// would fail elaboration if it were.
module cli_version;
  undeclared_t x;
endmodule
