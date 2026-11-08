extern module m(a, b, c, d);
extern module a #(parameter size = 8, parameter type TP = logic [7:0])
                (input [size:0] a, output TP b);

module top();
  wire a = 1'b1, b = 1'b0;
  wire c = 1'b1, d;
  m mm(.*);
  w ww();
  initial #1 $display("d %0d", d);
endmodule

module w();
  wire [8:0] a = 9'h101;
  logic [7:0] b;
  a aa(.*);
  initial #2 $display("b %0d size %0d bits %0d", b, aa.size, $bits(b));
endmodule

module m(.*);
  input a, b, c;
  output d;
  assign d = a & c & ~b;
endmodule

module a(.*);
  assign b = a[7:0] + 8'hA9;
endmodule
