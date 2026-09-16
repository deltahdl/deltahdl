// §16.13.2 Multiclocked properties: a clock may be written with any
// property, and the property is multiclocked where a subproperty has a
// clock other than the property's; its result is true or false, as a
// singly clocked property's is. A multiclocked sequence is a multiclocked
// property, true at a point where a match begins there; property operators
// join operands on different clocks, `(@(posedge clk0) sig0) and
// (@(posedge clk1) sig1)` being true at a point where both sequences have
// matches beginning there; the nonoverlapping implication |=> advances,
// from the end point of each match of the antecedent, to the nearest
// strictly subsequent tick of the consequent's clock, and the overlapping
// implication |-> to the nearest tick, the coincident one where the
// consequent's clock ticks at the end point; and if-else reads its
// condition at the property's clock and each branch at the nearest tick of
// the branch's clock, coincident or later. clk0 rises at 5, 15, ..., 75 so
// that tick n of it is at 10n - 5, the tick counter counting through; clk1
// rises at 12, 27, 45, 57 and 72, reading the counter as 2, 3, 5, 6 and 8,
// its tick at 45 together with clk0's fifth; and clk2 rises at 8, 25, 38,
// 55, 70 and 78, reading 1, 3, 4, 6, 7 and 8, its tick at 25 together with
// clk0's third. sig0 is high at 1, 2, 5 and 7, sig1 at 3 and 5, b at 1, 3
// and 6, s1 at 2 and 3 and s2 at 4 and 7.
//
// conj, the and of the two clocked booleans as the consequent of 1 |->,
// the and needing an antecedent so that the assertion has the unique
// semantic leading clock §16.16 (e) requires, begins at each tick of clk0:
// sig0 is read there and sig1 at the nearest tick of clk1, the same tick
// at 45, so the attempts from 15 and 45 hold, at 27 and 45, the ones from
// 5 and 65 fail at 12 and 72 with sig1 low, and the four with sig0 low
// fail at their tick. nonover, sig0 |=> @(posedge clk1) sig1, reads sig1
// at the tick of clk1 strictly after sig0's: the attempt from 15 holds at
// 27, those from 5, 45 and 65 fail at 12, 57 and 72, and the four with
// sig0 low hold. over, with |->, reads sig1 at the nearest tick of clk1,
// the same tick at 45, so the attempt from 45 holds there as well. ifelse
// reads b at each tick of clk0 and then s1 at the nearest tick of clk1 or
// s2 at the nearest tick of clk2: the attempts from 5, 25, 35 and 65 hold,
// at 12, 27, 38 and 70, and those from 15, 45, 55 and 75 fail, at 25, 55,
// 57 and 78.
module multiclock_properties;
  logic clk0 = 0;
  logic clk1 = 0;
  logic clk2 = 0;
  int tick = 1;
  logic sig0, sig1, b, s1, s2;
  int conj_pass = 0, conj_fail = 0;
  int nonover_pass = 0, nonover_fail = 0;
  int over_pass = 0, over_fail = 0;
  int ifelse_pass = 0, ifelse_fail = 0;
  string conj_at = "", nonover_at = "", over_at = "", ifelse_at = "";
  always #5 clk0 = ~clk0;
  always #10 tick = tick + 1;
  initial begin
    #12 clk1 = 1;
    #8 clk1 = 0;
    #7 clk1 = 1;
    #8 clk1 = 0;
    #10 clk1 = 1;
    #5 clk1 = 0;
    #7 clk1 = 1;
    #8 clk1 = 0;
    #7 clk1 = 1;
    #6 clk1 = 0;
  end
  initial begin
    #8 clk2 = 1;
    #8 clk2 = 0;
    #9 clk2 = 1;
    #7 clk2 = 0;
    #6 clk2 = 1;
    #8 clk2 = 0;
    #9 clk2 = 1;
    #7 clk2 = 0;
    #8 clk2 = 1;
    #4 clk2 = 0;
    #4 clk2 = 1;
    #1 clk2 = 0;
  end

  assign sig0 = tick inside {1, 2, 5, 7};
  assign sig1 = tick inside {3, 5};
  assign b = tick inside {1, 3, 6};
  assign s1 = tick inside {2, 3};
  assign s2 = tick inside {4, 7};

  conj: assert property (@(posedge clk0)
                         1 |-> (@(posedge clk0) sig0) and (@(posedge clk1) sig1))
    begin
      conj_pass++;
      conj_at = $sformatf("%s %0d", conj_at, $time);
    end else conj_fail++;

  nonover: assert property (@(posedge clk0) sig0 |=> @(posedge clk1) sig1)
    begin
      nonover_pass++;
      nonover_at = $sformatf("%s %0d", nonover_at, $time);
    end else nonover_fail++;

  over: assert property (@(posedge clk0) sig0 |-> @(posedge clk1) sig1)
    begin
      over_pass++;
      over_at = $sformatf("%s %0d", over_at, $time);
    end else over_fail++;

  ifelse: assert property (@(posedge clk0)
                           if (b) @(posedge clk1) s1 else @(posedge clk2) s2)
    begin
      ifelse_pass++;
      ifelse_at = $sformatf("%s %0d", ifelse_at, $time);
    end else ifelse_fail++;

  initial begin
    #80;
    $display("1 |-> (@(posedge clk0) sig0) and (@(posedge clk1) sig1) passes %0d fails %0d at%s",
             conj_pass, conj_fail, conj_at);
    $display("sig0 |=> @(posedge clk1) sig1 passes %0d fails %0d at%s",
             nonover_pass, nonover_fail, nonover_at);
    $display("sig0 |-> @(posedge clk1) sig1 passes %0d fails %0d at%s",
             over_pass, over_fail, over_at);
    $display("if (b) @(posedge clk1) s1 else @(posedge clk2) s2 passes %0d fails %0d at%s",
             ifelse_pass, ifelse_fail, ifelse_at);
    $finish;
  end
endmodule
