// §16.14.6.3 Procedural concurrent assertions and glitches: a procedural
// concurrent assertion is immune to a glitch the order of procedural
// execution would cause, the flush of the queue dropping the instance a
// procedure queued on a value that had not settled, but not to one an
// execution loop between regions causes, code in the Reactive region that
// modifies a signal bringing another pass of the Active region, whose
// newly queued instance begins a second attempt too late to prevent the
// report the Observed region already made. clk rises at 5, 15, 25 and 35,
// bar toggles at each posedge, and the run ends at 40.
//
// The clause's procedural_block_1 assigns bar to foo while en is 1, and
// its procedural_block_2 asserts p1, const'(foo) == const'(bar) at posedge
// clk. While en is 1, at 5 and 15, procedural_block_2 may run once on the
// change of bar, queueing an instance that would fail, and again after the
// assignment that updates foo, which flushes the first, so p1 passes and
// no glitch is reported; the instance queued when the two procedures first
// ran, at 0, passes at 5 as well. From 20 en is 0 and foo takes bar from
// the program instead, in the Reactive region, so at 25 and 35 the
// instance queued on the change of bar matures and fails in the Observed
// region, and the instance queued after the program's assignment, in the
// Active region that follows, passes in the same time step, too late to
// prevent the report. procedural_block_1 assigns foo under en alone, as
// the clause writes it, which the tool notes may infer a latch (§9.2.2.2).
module procedural_assertion_glitches;
  logic clk = 0;
  logic en = 1, foo = 0, bar = 0;
  always #5 clk = ~clk;
  always @(posedge clk) bar <= ~bar;

  always_comb begin : procedural_block_1
    if (en) foo = bar;
  end

  always_comb begin : procedural_block_2
    p1: assert property (@(posedge clk) (const'(foo) == const'(bar)))
      $display("p1 passed at %0d", $time);
    else $display("p1 failed at %0d", $time);
  end

  program reactive_driver;
    initial forever @(posedge clk) if (!en) foo = bar;
  endprogram

  initial begin
    #20 en = 0;
    #20 $finish;
  end
endmodule
