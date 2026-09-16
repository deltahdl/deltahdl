// §16.16.1 Semantic leading clock of a multiclocked property: a
// multiclocked property has a unique semantic leading clock only where all
// its leading clocks are identical, two clocks of the same value written
// differently being not identical, and the inherited clock refers to the
// incoming outer clock, the statement's leading clocking event or, in a
// procedural block, the one contextually inferred. clk1 toggles every 5
// from 0 and clk2 is assigned clk1, so the two have the same value at
// every time and are still not identical; b is 1 from 12 to 22 and c from
// 22 to 32, a stays 1, and the run ends at 40.
//
// a2 is the clause's, @(clk1) a and @(clk1) b, whose second operand is
// clocked by the very clock flowing in, so its leading clocks are one and
// it is legal; it passes at the ticks of clk1, every change, where b is 1,
// 15 and 20. a4 is the clause's, a and @(posedge clk1) c in an always at
// posedge clk1, the inferred clock and the operand's identical, so it is
// legal too and passes at 25, the posedge where c is 1. c1 covers a
// sequence clocked by posedge clk1 that switches to negedge clk1 after its
// first tick, whose leading clock is the first and unique: it attempts at
// 5, 15, 25 and 35 and is covered at 30, the negedge after 25 where c is
// 1. The clause's a1, @(clk1) a and @(clk2) b, and a3, a and @(posedge
// clk2) in an always at posedge clk1, are illegal and stay out of the
// design.
module semantic_leading_clocks;
  logic clk1 = 0;
  wire clk2;
  logic a = 1, b = 0, c = 0;
  assign clk2 = clk1;
  always #5 clk1 = ~clk1;

  a2: assert property (@(clk1) a and @(clk1) b)
    $display("a2 passed at %0d", $time); else;

  always @(posedge clk1) begin
    a4: assert property (a and @(posedge clk1) c)
      $display("a4 passed at %0d", $time); else;
  end

  c1: cover property (@(posedge clk1) a ##1 @(negedge clk1) c)
    $display("c1 covered at %0d", $time);

  initial begin
    #12 b = 1;
    #10 b = 0; c = 1;
    #10 c = 0;
    #8 $finish;
  end
endmodule
