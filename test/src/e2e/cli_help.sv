// --help answers with the version and the list of options and exits 0 without
// reading the source named beside it, which is never compiled: the module here
// would fail elaboration if it were.
module cli_help;
  undeclared_t x;
endmodule
