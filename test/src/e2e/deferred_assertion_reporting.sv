// §16.4.1 Deferred assertion reporting: when a deferred assertion passes or
// fails, its action block's subroutine call, or the default $error of a failing
// assert or assume with no else, is placed in the deferred assertion report
// queue of the executing process as a pending report rather than executed. A
// process reaching a flush point clears its queue, and the pending reports are
// never executed. In the Observed region each pending observed report that was
// not flushed matures and may no longer be flushed; its call is executed in the
// Reactive region. In the Postponed region each pending final report that was
// not flushed matures and its call is scheduled in that same region. Code in
// the Reactive region that modifies a signal causes another pass through the
// Active region, which may re-execute an observed deferred assertion with a
// different result, a glitch the final form does not suffer.
module deferred_assertion_reporting;
  int a = 1;
  event go;
  event go2;

  task automatic note(input string what);
    $display("%s", what);
  endtask

  function void set_a_1;
    a = 1;
  endfunction

  task fire_go2;
    -> go2;
  endtask

  always_comb begin : b1
    a1: assert #0 (a == 1) note("a1: a is 1"); else note("a1: a is not 1");
    f1: assert final (a == 1) note("f1: a is 1"); else note("f1: a is not 1");
  end

  initial begin
    #5;
    // A flush point before the reports mature: ->> triggers go from the NBA
    // region, the process resumes in the Active region that follows, and its
    // queue is cleared before the Observed region matures anything, so none
    // of the three reports, the default $error among them, is executed.
    ->> go;
    assert #0 (1) note("flushed: an observed report that is never executed");
    assert final (1) note("flushed: a final report that is never executed");
    assert #0 (0);
    @(go);
    $display("at 5: resumed at the flush point, the three reports cleared");

    #5;
    // The observed report matures in the Observed region before the process
    // reaches its next flush point, which one of the reports itself causes:
    // fire_go2 runs in the Reactive region and the process resumes after it.
    // The final report queued beside them has not matured by then and is
    // flushed.
    assert #0 (1) note("at 10: matured, reported before the process resumes");
    assert final (1) note("flushed: a final report pending across the resume");
    cover #0 (1) fire_go2();
    @(go2);
    $display("at 10: resumed after go2 was triggered in the Reactive region");

    #10;
    // Writing 2 re-runs b1, which queues its two reports. The observed cover
    // action then writes 1 in the Reactive region, after b1's observed report
    // has matured, so that report is executed, and the write sends b1 through
    // the Active region again: the re-run flushes the final report that had
    // not matured, and both assertions report the settled value.
    a = 2;
    cover #0 (1) set_a_1();

    #5;
    // A default $error that is not flushed is executed in the Reactive region.
    assert #0 (a == 5);
    #1 $finish;
  end
endmodule
