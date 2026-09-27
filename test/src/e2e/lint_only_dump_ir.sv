// --dump-ir prints the elaborated design, and --lint-only then stops the run
// before simulation, so the dump is printed and the $display never runs.
module lint_only_dump_ir;
  logic a = 1;
  initial $display("ran");
endmodule
