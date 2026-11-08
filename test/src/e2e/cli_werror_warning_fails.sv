module cli_werror_warning_fails;
  logic a = 1, b;
  always_comb if (a) b = 1;
  initial #1 $display("ran");
endmodule
