// §16.15 Disable iff resolution: a default disable iff declaration in a
// module, interface, program or generate block gives a default disable
// condition to every concurrent assertion in its scope and subscopes, the
// nested declarations and generate blocks among them, unless one of those
// declares a default of its own, which overrides it there; the effect is
// independent of the declaration's position in the scope, and the scope
// does not extend into an instance of a module declared elsewhere. The
// disable condition of an assertion is then, in this order, the one its
// own disable iff clause names, the default disable iff in scope, or none,
// which is 1'b0. clk rises at 5, 15, 25 and 35, a is 1 and b 0 throughout,
// so every attempt of a |=> b fails at the tick after its own unless its
// disable condition holds at either, rst is 1 across the tick of 15 and
// rst1 across the tick of 35, and the run ends at 40, the attempts of 35
// still in flight holding there.
//
// The clause's examples_with_default declares rst its default: its a1
// names rst1 itself and its a2 through p1, so both fail at 15 and 25 and
// are disabled at 35; its a3 infers rst, disabled at 15 and failing at 35;
// its a4 names 1'b0, the one way to cancel the default, failing at every
// tick. The nested m2 declares no default and inherits rst, so a_m2 fails
// at 35 alone, and the nested m3 declares rst1 its own, so a_m3 fails at
// 15 and 25. The clause's examples_without_default declares none: its a5
// names rst and its a6 has it from p2, both failing at 35, and its a7 has
// no disable condition, failing at every tick.
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
