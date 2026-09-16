// §16.18 Clocking blocks and concurrent assertions: a variable used in a
// concurrent assertion that is a clocking block variable is sampled only in
// the clocking block, so the assertion reads the value the block captured
// at its clocking event. The clause's module A declares cb_with_input,
// whose input a is a clocking block variable and whose p1 asserts a,
// cb_without_input, whose p1 asserts the module's a, the property p1
// asserting a at posedge clk and p2 asserting cb_with_input.a, and its
// a1 to a4 assert p1, cb_with_input.p1, p2 and cb_without_input.p1, which
// the clause has equivalent: the block samples a at posedge clk, its
// default input skew 1step, where the assertion samples a as well. As in
// the clause's Figure 16-17, clk rises at 5, 15, 25, 35, 45 and 55, and a
// rises at 20, between the second and the third rising edge, and falls at
// 40, between the fourth and the fifth, so every one of the four passes
// at 25 and at 35, where the sampled a is 1, and fails at the other edges,
// where its else clause says nothing; the run ends at 60.
module A(input logic clk, input logic a);
  clocking cb_with_input @(posedge clk);
    input a;
    property p1;
      a;
    endproperty
  endclocking

  clocking cb_without_input @(posedge clk);
    property p1;
      a;
    endproperty
  endclocking

  property p1;
    @(posedge clk) a;
  endproperty

  property p2;
    @(posedge clk) cb_with_input.a;
  endproperty

  a1: assert property (p1) $display("a1 passed at %0d", $time); else;
  a2: assert property (cb_with_input.p1)
    $display("a2 passed at %0d", $time); else;
  a3: assert property (p2) $display("a3 passed at %0d", $time); else;
  a4: assert property (cb_without_input.p1)
    $display("a4 passed at %0d", $time); else;
endmodule

module clocking_block_assertions;
  logic clk = 0;
  logic a = 0;
  always #5 clk = ~clk;
  A u1(clk, a);
  initial begin
    #20 a = 1;
    #20 a = 0;
    #20 $finish;
  end
endmodule
