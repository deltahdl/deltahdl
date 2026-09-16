// §16.14.6 Embedding concurrent assertions in procedural code: a concurrent
// assertion statement in a procedural block is not evaluated where it is
// reached; the assertion is placed in the procedural assertion queue of
// the process as a pending instance, a statement a loop reaches several
// times placing as many, and in the Observed region of each time step
// every pending instance matures: if the assertion's leading clocking
// event occurred in the step, an evaluation attempt begins at once, and
// otherwise the matured instance waits for the next occurrence of the
// event. A property with no clocking event of its own takes the clock
// inferred from the procedure, where the procedure holds no blocking
// timing control and exactly one event control, one and only one event
// expression of which is an edge over an expression, with or without an
// iff, or solely an event variable or clocking block identifier, and names
// nothing the procedure references elsewhere but as a clocking event or
// within an assertion; where the procedure gives none, the default
// clocking is the clock, as if the assertion stood before the procedure.
//
// The clause's r1, q != d, is asserted in the procedure clocked by mclk,
// which rises at 10, 30, ..., 110, and q <= d1 there; d is 1 throughout
// and d1 is 1 from 25 to 65, so q is 1 across the ticks of 50 and 70,
// where r1 fails, and 0 at the other four. r1_p1 takes the inferred
// posedge mclk, so it passes four times and fails twice. r1_p2 is clocked
// by scanclk as written, rising at 20, 60 and 100, half the frequency of
// mclk: the instance queued at 10 is evaluated at 20, the two queued at 30
// and 50 both at 60, where each fails, and the two queued at 70 and 90
// both at 100, so every posedge of scanclk sees r1_p2 evaluated twice, and
// the instance of 110 waits when the run ends. r1_p3 is clocked by
// fastclk, rising at 5, 15, ..., 115, twice the frequency of mclk: the
// instance queued at each posedge of mclk is evaluated at the posedge of
// fastclk after it, so only every other posedge of fastclk evaluates
// r1_p3, at 15, 35, 55, 75, 95 and 115. loop_p is reached three times at
// each posedge of mclk, so three instances mature there and r1 is
// evaluated three times; c_p covers q == d1, true at 10, 50, 90 and 110.
// The clause's r2 is asserted in the always_ff clocked by posedge clock
// iff reset == 0 or posedge reset, clock rising at 15, 45, 75 and 105 and
// reset high from 40 to 50: posedge reset names reset, which the procedure
// references, so the inferred clock is posedge clock iff reset == 0; the
// instance queued at 40, when reset rose, finds no such event in its step
// and waits, the event of 45 not occurring while reset is high, so at 75
// two instances are evaluated, and r2 fails at 75 twice and at 105 once,
// q2 having taken d2 at 15. r4_p stands in an initial procedure after a
// delay, which is a blocking timing control, so no clock is inferred and
// the default clocking, posedge scanclk, is its clock: queued at 12, it is
// evaluated at 20, where r1 holds. The run ends at 120.
module procedural_concurrent_assertions;
  logic mclk = 0, scanclk = 0, fastclk = 0, clock = 0;
  logic reset = 0;
  logic d1 = 0, d = 1, q = 0;
  logic d2 = 1, q2 = 0;
  int cnt = 0;
  int p1_pass = 0, p1_fail = 0, loop_pass = 0, loop_fail = 0;
  int p4_pass = 0, p4_fail = 0, c_hits = 0;
  always #10 mclk = ~mclk;
  always #20 scanclk = ~scanclk;
  always #5 fastclk = ~fastclk;
  always #15 clock = ~clock;

  default clocking dc @(posedge scanclk); endclocking

  property r1;
    q != d;
  endproperty
  always @(posedge mclk) begin
    q <= d1;
    r1_p1: assert property (r1) p1_pass++; else p1_fail++;
    r1_p2: assert property (@(posedge scanclk) r1)
      $display("r1_p2 passed at %0d", $time);
    else $display("r1_p2 failed at %0d", $time);
    r1_p3: assert property (@(posedge fastclk) r1)
      $display("r1_p3 passed at %0d", $time);
    else $display("r1_p3 failed at %0d", $time);
    for (int i = 0; i < 3; i++)
      loop_p: assert property (r1) loop_pass++; else loop_fail++;
    c_p: cover property (q == d1) c_hits++;
  end

  property r2;
    q2 != d2;
  endproperty
  always_ff @(posedge clock iff reset == 0 or posedge reset) begin
    cnt <= reset ? 0 : cnt + 1;
    q2 <= d2;
    r2_p: assert property (r2);
  end

  initial begin
    #12;
    r4_p: assert property (r1) p4_pass++; else p4_fail++;
  end

  initial begin
    #25 d1 = 1;
    #15 reset = 1;
    #10 reset = 0;
    #15 d1 = 0;
    #55 $display("r1_p1 passes %0d fails %0d", p1_pass, p1_fail);
    $display("loop_p passes %0d fails %0d", loop_pass, loop_fail);
    $display("r4_p passes %0d fails %0d", p4_pass, p4_fail);
    $display("c_p covered %0d times", c_hits);
    $finish;
  end
endmodule
