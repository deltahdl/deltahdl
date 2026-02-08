module if_else;
  logic [7:0] x;

  initial begin
    x = 5;
    if (x == 5)
      $display("x is five");
    else
      $display("x is not five");

    x = 10;
    if (x == 5)
      $display("still five");
    else
      $display("not five anymore");
  end
endmodule
