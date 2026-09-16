// IEEE 1800-2023 16.2 (printed page 383) rules on what an assertion statement
// is and how it is evaluated. It is one of four kinds: an assert, checked to
// verify the property holds; an assume, which simulators check as they check
// an assert; a cover, which monitors the property's evaluation for coverage;
// and a restrict, a constraint on formal verification whose property
// simulators do not check. And it is one of two kinds: an immediate assertion
// follows simulation event semantics and executes like a statement in a
// procedural block, while a concurrent assertion follows clock semantics, so
// any event between clock edges is abstracted away. There is no immediate
// restrict, which the parser refuses and a unit test reads.
//
// This design holds the three checkable kinds in both forms and a restrict
// property, all over one signal, ok, driven high except for two low pulses:
// a glitch from 12 to 13 that falls between the clock edges at 5 and 15, and
// a pulse from 22 to 28 that the edge at 25 sees. The immediate assertions
// sit in a procedural block sensitive to ok, so event semantics runs them at
// each of ok's four changes and they see both pulses: the assert and the
// assume fail twice, first at 12, and the cover of !ok hits twice. The
// concurrent assertions see the signal at the edges alone, at 5, 15, 25 and
// 35, so the glitch is abstracted away and each sees one low tick at 25: the
// assert and the assume fail once, and the cover hits once. The restrict
// property is written on the same signal and does not hold at 25, and being
// unchecked in simulation it reports nothing, not even a notice that it went
// unevaluated, since that is the clause's rule rather than a gap.
//
// The action blocks count rather than print, since the three concurrent
// assertions fire in one time step and the clause fixes no order among them;
// the counts and the recorded times are printed once, after the last edge.
// The lines after $finish are the end-of-simulation reports: 16.3's for the
// immediate cover statement, evaluated at each of ok's four changes and
// succeeding at the two falls, and 16.14.3's for the concurrent cover,
// attempted at the four edges and succeeding at 25.
module assertion_kinds;
  logic clk = 1'b0;
  logic ok = 1'b1;
  int concurrent_assert_fails = 0;
  int concurrent_assume_fails = 0;
  int concurrent_cover_hits = 0;
  int immediate_assert_fails = 0;
  int immediate_assume_fails = 0;
  int immediate_cover_hits = 0;
  time concurrent_assert_fail_time = 0;
  time immediate_assert_fail_time = 0;

  always #5 clk = ~clk;

  assert property (@(posedge clk) ok)
  else begin
    concurrent_assert_fails = concurrent_assert_fails + 1;
    concurrent_assert_fail_time = $time;
  end

  assume property (@(posedge clk) ok)
  else concurrent_assume_fails = concurrent_assume_fails + 1;

  cover property (@(posedge clk) !ok)
    concurrent_cover_hits = concurrent_cover_hits + 1;

  restrict property (@(posedge clk) ok);

  always @(ok) begin
    assert (ok)
    else begin
      if (immediate_assert_fails == 0) immediate_assert_fail_time = $time;
      immediate_assert_fails = immediate_assert_fails + 1;
    end
    assume (ok)
    else immediate_assume_fails = immediate_assume_fails + 1;
    cover (!ok) immediate_cover_hits = immediate_cover_hits + 1;
  end

  initial begin
    #12 ok = 1'b0;
    #1 ok = 1'b1;
    #9 ok = 1'b0;
    #6 ok = 1'b1;
    #12;
    $display("concurrent assert: failed %0d time, at %0d",
             concurrent_assert_fails, concurrent_assert_fail_time);
    $display("concurrent assume: failed %0d time", concurrent_assume_fails);
    $display("concurrent cover: hit %0d time", concurrent_cover_hits);
    $display("immediate assert: failed %0d times, first at %0d",
             immediate_assert_fails, immediate_assert_fail_time);
    $display("immediate assume: failed %0d times", immediate_assume_fails);
    $display("immediate cover: hit %0d times", immediate_cover_hits);
    $finish;
  end
endmodule
