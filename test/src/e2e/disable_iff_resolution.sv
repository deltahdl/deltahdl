module examples_with_default(input logic a, b, clk, rst, rst1);
  default disable iff rst;
  property p1;
    disable iff (rst1) a |=> b;
  endproperty

  a1: assert property (@(posedge clk) disable iff (rst1) a |=> b);
  a2: assert property (@(posedge clk) p1);
  a3: assert property (@(posedge clk) a |=> b);
  a4: assert property (@(posedge clk) disable iff (1'b0) a |=> b);

  module m2;
    a_m2: assert property (@(posedge clk) a |=> b);
  endmodule

  module m3;
    default disable iff rst1;
    a_m3: assert property (@(posedge clk) a |=> b);
  endmodule
endmodule

module examples_without_default(input logic a, b, clk, rst);
  property p2;
    disable iff (rst) a |=> b;
  endproperty

  a5: assert property (@(posedge clk) disable iff (rst) a |=> b);
  a6: assert property (@(posedge clk) p2);
  a7: assert property (@(posedge clk) a |=> b);
endmodule

module disable_iff_resolution;
  logic clk = 0;
  logic a = 1, b = 0, rst = 0, rst1 = 0;
  always #5 clk = ~clk;

  examples_with_default u1(a, b, clk, rst, rst1);
  examples_without_default u2(a, b, clk, rst);

  initial begin
    #12 rst = 1;
    #6 rst = 0;
    #14 rst1 = 1;
    #6 rst1 = 0;
    #2 $finish;
  end
endmodule
