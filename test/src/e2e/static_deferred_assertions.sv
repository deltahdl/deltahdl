module m (input logic [3:0] a, input logic [3:0] b);
  a1: assert #0 (a == b) else $error("a1: a is %0d and b is %0d", a, b);
  f1: assert final (a == b) else $error("f1: a is %0d and b is %0d", a, b);
  c1: cover #0 (a != b) $display("c1: covered a %0d against b %0d", a, b);
endmodule

module static_deferred_assertions;
  logic [3:0] a = 0;
  logic [3:0] b = 0;
  m u (.a(a), .b(b));

  initial begin
    #10 a = 5;
    #10 b = 5;
    #10 a = 7;
    #0 b = 7;
    #10 $finish;
  end
endmodule
