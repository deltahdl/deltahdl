// §16.12.20 Property examples: the clause's rule1 to rule5a, run as the
// property_spec of an assertion each. The assertions run over eight ticks,
// clk rising at 5, 15, ..., 75 so that tick n is at 10n - 5, and clkev, the
// clock rule2 names, toggling at each rising edge: a is high at 1, 2, 3 and
// 6, b at 1, 4 and 6, c at 2, 3 and 7, d at 2, 3, 5 and 7, e at 5 and 8,
// and f at 3.
//
// rule1, a |-> b ##1 c ##1 d: the attempt from 1 holds at 3, those from 2
// and 3 fail at their tick with b low, the one from 6 fails at 8 with d
// low, and the four with a low hold at their tick. rule2 negates the same
// sequence in the consequent under disable iff (e): the attempt from 1
// fails at 3, those from 2 and 3 hold with b low, the one from 4 holds
// with a low, the attempt from 6 is dropped at 8, where e disables the
// property, as is any that would begin at 5 or 8, and the one from 7
// holds. rule3, a[*2] |-> ((##[1:3] c) or (d |=> e)): the attempt from 1
// has its antecedent at 2 and c at 3, so it holds at 3; the one from 2 has
// its antecedent at 3, no c at 4 to 6 and no e at 4 after d at 3, so it
// fails at 6; the six others hold, at the tick after a where a holds
// alone. rule4 joins the same operands under and: the attempt from 1 fails
// at 3, where e is low after d at 2, the one from 2 at 4, and the six
// others hold. rule5, a ##1 (b || c)[->1] |-> if (b) (##1 d |-> e) else
// f: the attempt from 1 reaches c at 2 and, b being low, f, low, so it
// fails at 2; the one from 2 reaches c at 3 and f, high, so it holds at 3;
// the one from 3 reaches b at 4 and d at 5 with e high, so it holds at 5;
// the one from 6 reaches c at 7 and f, low, so it fails at 7; the four
// others hold at their tick. rule5a is rule5 through an instance of rule6.
module property_examples;
  logic clk = 0;
  logic clkev = 0;
  int tick = 1;
  logic a, b, c, d, e, f;
  int r1_pass = 0, r1_fail = 0;
  int r2_pass = 0, r2_fail = 0;
  int r3_pass = 0, r3_fail = 0;
  int r4_pass = 0, r4_fail = 0;
  int r5_pass = 0, r5_fail = 0;
  int r5a_pass = 0, r5a_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;
  always @(posedge clk) clkev <= ~clkev;

  assign a = tick inside {1, 2, 3, 6};
  assign b = tick inside {1, 4, 6};
  assign c = tick inside {2, 3, 7};
  assign d = tick inside {2, 3, 5, 7};
  assign e = tick inside {5, 8};
  assign f = tick inside {3};

  property rule1;
    @(posedge clk) a |-> b ##1 c ##1 d;
  endproperty

  property rule2;
    @(clkev) disable iff (e) a |-> not (b ##1 c ##1 d);
  endproperty

  property rule3;
    @(posedge clk) a[*2] |-> ((##[1:3] c) or (d |=> e));
  endproperty

  property rule4;
    @(posedge clk) a[*2] |-> ((##[1:3] c) and (d |=> e));
  endproperty

  property rule5;
    @(posedge clk)
    a ##1 (b || c)[->1] |->
      if (b)
        (##1 d |-> e)
      else // c
        f;
  endproperty

  property rule6(x, y);
    ##1 x |-> y;
  endproperty

  property rule5a;
    @(posedge clk)
    a ##1 (b || c)[->1] |->
      if (b)
        rule6(d, e)
      else // c
        f;
  endproperty

  r1: assert property (rule1) r1_pass++; else r1_fail++;
  r2: assert property (rule2) r2_pass++; else r2_fail++;
  r3: assert property (rule3) r3_pass++; else r3_fail++;
  r4: assert property (rule4) r4_pass++; else r4_fail++;
  r5: assert property (rule5) r5_pass++; else r5_fail++;
  r5a: assert property (rule5a) r5a_pass++; else r5a_fail++;

  initial begin
    #80;
    $display("rule1 passes %0d fails %0d at ticks", r1_pass, r1_fail);
    $display("rule2 passes %0d fails %0d at ticks", r2_pass, r2_fail);
    $display("rule3 passes %0d fails %0d at ticks", r3_pass, r3_fail);
    $display("rule4 passes %0d fails %0d at ticks", r4_pass, r4_fail);
    $display("rule5 passes %0d fails %0d at ticks", r5_pass, r5_fail);
    $display("rule5a passes %0d fails %0d at ticks", r5a_pass, r5a_fail);
    $finish;
  end
endmodule
