module top;
  int y;
  int z = f();
  logic [W-1:0] v;
  initial begin
    y = g;
    $display("%0d %0d %0d", y, z, $bits(v));
    $finish;
  end
endmodule
