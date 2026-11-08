module string_param_named;
  parameter string A = "John Smith";
  parameter string B = A;
  initial $display("%s", B);
endmodule
