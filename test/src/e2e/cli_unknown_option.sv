// An option deltahdl does not know stops the run before any source is read,
// with status 1: the module here would print if it were simulated.
module cli_unknown_option;
  initial $display("ran");
endmodule
