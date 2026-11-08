`define W 8
typedef logic [3:0] t;
module top;
  localparam int AW = $bits(t);
  child c();
  split s();
  initial begin
    $display("%0d %0d %0d %0d", AW, c.bw, c.seen, s.k);
    $finish;
  end
endmodule
