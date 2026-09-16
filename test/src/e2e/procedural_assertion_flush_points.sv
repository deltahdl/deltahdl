// §16.14.6.2 Procedural assertion flush points: a process reaches one when
// it resumes after suspending at an event control or a wait statement,
// when, declared by always_comb or always_latch, it resumes on a
// transition of a dependent signal, or when its outermost scope is
// disabled, and its procedural assertion queue is then cleared, so a
// pending instance does not mature unless the procedure queues it again,
// where an instance that matured in an earlier Observed region is kept.
// clk rises at 5, 15, ..., 45, and every assertion below takes the default
// clocking, posedge clk, the always_comb procedures holding no event
// control and b1 a delay; the run ends at 50.
//
// The clause's a1, const'(not_a) != const'(a) in the always_comb b1, is
// queued at each change of a, once with not_a still holding its previous
// value where the procedure runs before the continuous assignment does,
// and once more, after the flush the assignment's transition brings, with
// not_a updated, so no failure is ever reported: the procedure runs at 0
// and a changes at 15, with the clock edge, and at 20, without, so a1
// passes three times, at 5, 15 and 25. The clause's a2 and
// a3 stand either side of a delay in b2, always @(a2_a or a2_b): a2 is
// queued at 10, when a2_a rises, with the values 1 and 0 saved, and
// matures in the Observed region before the delay ends; a3 is queued at
// 11, after it, with the same values, and a2_b is assigned a2_a after it,
// nonblocking, so the procedure, back at its event control, resumes at 11
// on a2_b's transition, which flushes a3 before it matures, and queues a2
// with 1 and 1, then a3 with 1 and 1 at 12, so at 15 a2 fails and passes
// and a3 passes once. The clause's c1 covers const'(cb) !=
// const'(ca) in the always_comb b3 while both are driven from src, which
// changes at 25 and 35: the procedure may run between the two assignments,
// queueing a glitch, but the second assignment's transition flushes it and
// the instance queued after finds the two equal, so c1 is attempted at 5,
// 25 and 35 and never covered.
module procedural_assertion_flush_points;
  logic clk = 0;
  logic a = 0, not_a;
  logic a2_a = 0, a2_b = 0;
  logic src = 0, ca, cb;
  int a1_pass = 0, a1_fail = 0;
  always #5 clk = ~clk;
  assign not_a = !a;
  assign ca = src;
  assign cb = src;

  default clocking @(posedge clk); endclocking

  always_comb begin : b1
    a1: assert property (const'(not_a) != const'(a)) a1_pass++;
    else a1_fail++;
  end

  always @(a2_a or a2_b) begin : b2
    a2: assert property (const'(a2_a) == const'(a2_b))
      $display("a2 passed at %0d", $time);
    else $display("a2 failed at %0d", $time);
    #1;
    a3: assert property (const'(a2_a) == const'(a2_b))
      $display("a3 passed at %0d", $time);
    else $display("a3 failed at %0d", $time);
    a2_b <= a2_a;
  end

  always_comb begin : b3
    c1: cover property (const'(cb) != const'(ca));
  end

  initial begin
    #10 a2_a = 1;
    #5 a = 1;
    #5 a = 0;
    #5 src = 1;
    #10 src = 0;
    #15 $display("a1 passes %0d fails %0d", a1_pass, a1_fail);
    $finish;
  end
endmodule
