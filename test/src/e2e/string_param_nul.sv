module string_param_nul;
  parameter string S = "a\0b";
  localparam int N = S.len();
  initial begin
    $display("%0d", N);
    $display("%0d", S.len());
    $display("%s", S);
  end
endmodule
