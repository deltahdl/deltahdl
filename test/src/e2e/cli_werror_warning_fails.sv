// -Werror makes every warning an error. The always_comb below assigns b on only
// one path, which draws the §9.2.2.2 warning that it may infer a latch, so with
// -Werror the run fails with status 1 and the design is never simulated.
module cli_werror_warning_fails;
  logic a = 1, b;
  always_comb if (a) b = 1;
  initial #1 $display("ran");
endmodule
