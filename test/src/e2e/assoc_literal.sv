module assoc_literal;
  integer tab [string] = '{"Peter":20, "Paul":22, "Mary":23, default:0};
  initial begin
    $display("%0d", tab["Peter"]);
    $display("%0d", tab["Paul"]);
    $display("%0d", tab["Mary"]);
    $display("%0d", tab["unknown"]);
  end
endmodule
