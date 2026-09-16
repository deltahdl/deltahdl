// §16.16 Clock resolution: the leading clocking event of a concurrent
// assertion statement is, (d), the one it specifies explicitly; (c) else,
// in a procedural block, the one contextually inferred, which supersedes
// the default clocking; (a) else the default clocking event of the scope,
// treated as though written explicitly, which applies to the statement and
// not to a sequence or property declaration unless the declaration stands
// in a clocking block whose event is the default; (b) a declaration in a
// clocking block is clocked by the block's event, and is named through the
// block where an assertion instantiates it; and (f) a statement with none
// of the three is legal only where its maximal property is an instance of
// a sequence or property for which a unique leading clocking event is
// determined. clk rises at 5, 15, 25 and 35 and falls at 10, 20, 30 and
// 40, a is 1 across the ticks of 15 and 20 and b across those of 25 and
// 30, so an attempt of a |=> !b at 15 fails at 25 and one at 20 at 30,
// every other attempt holding vacuously, a ##1 b matches from 15 at 25 and
// from 20 at 30, and the run ends at 40, before the negedge of that time
// begins an attempt. The time an assertion fails or a cover is covered
// names its clock: 25 for posedge clk, 30 for negedge.
//
// In examples_with_default, whose default clocking is posedge_clk, d1
// instantiates the unclocked q1 and d2 writes the unclocked spec, both on
// the default, d3 writes negedge clk, d4 instantiates posedge_clk.q3, on
// the block's clock, and d5 instantiates q5, on the clock q5 declares; in
// the always at negedge clk, p1 instantiates q1 on the inferred negedge
// and p2 instantiates posedge_clk.q3, queued at negedge clk and checked at
// the next posedge; c1 covers s2 on the default and c2 on negedge clk. In
// examples_without_default, e1 instantiates q5 and e3 s3, each on the
// clock its declaration determines, and e2 writes negedge clk.
module examples_with_default(input logic a, b, clk);
  property q1;
    a |=> !b;
  endproperty
  default clocking posedge_clk @(posedge clk);
    property q3;
      a |=> !b;
    endproperty
  endclocking
  property q5;
    @(negedge clk) a |=> !b;
  endproperty
  sequence s2;
    a ##1 b;
  endsequence

  d1: assert property (q1) else $display("d1 failed at %0d", $time);
  d2: assert property (a |=> !b) else $display("d2 failed at %0d", $time);
  d3: assert property (@(negedge clk) a |=> !b)
    else $display("d3 failed at %0d", $time);
  d4: assert property (posedge_clk.q3)
    else $display("d4 failed at %0d", $time);
  d5: assert property (q5) else $display("d5 failed at %0d", $time);

  always @(negedge clk) begin
    p1: assert property (q1) else $display("p1 failed at %0d", $time);
    p2: assert property (posedge_clk.q3)
      else $display("p2 failed at %0d", $time);
  end

  c1: cover property (s2) $display("c1 covered at %0d", $time);
  c2: cover property (@(negedge clk) s2)
    $display("c2 covered at %0d", $time);
endmodule

module examples_without_default(input logic a, b, clk);
  property q5;
    @(negedge clk) a |=> !b;
  endproperty
  sequence s2;
    a ##1 b;
  endsequence
  sequence s3;
    @(negedge clk) s2;
  endsequence

  e1: assert property (q5) else $display("e1 failed at %0d", $time);
  e2: cover property (@(negedge clk) s2)
    $display("e2 covered at %0d", $time);
  e3: cover property (s3) $display("e3 covered at %0d", $time);
endmodule

module clock_resolution;
  logic clk = 0;
  logic a = 0, b = 0;
  always #5 clk = ~clk;

  examples_with_default u1(a, b, clk);
  examples_without_default u2(a, b, clk);

  initial begin
    #12 a = 1;
    #10 a = 0; b = 1;
    #12 b = 0;
    #6 $finish;
  end
endmodule
