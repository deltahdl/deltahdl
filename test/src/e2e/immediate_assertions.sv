// IEEE 1800-2023 16.3 (printed pages 383 to 386) rules on the immediate
// assertion statement, a test of an expression made when the statement
// executes in procedural code. This design runs one statement for each rule
// and prints which way it went, and the expected output is what the clause
// says of each:
//
// The expression is read as an if condition: x, z and 0 are false and the
// assertion fails, anything else is true and it passes. Four values, three
// failing and one passing, show the boundary.
//
// The action block's first statement is the pass statement, run when the
// expression is true, and the else statement is the fail statement, run when
// it is false. Either can be omitted: with no pass statement a true assertion
// does nothing the user wrote, and with no else a false assertion has the
// tool call $error by default, whose report goes to standard error. An
// assume is checked as an assert is. A cover runs its pass statement when the
// expression is true, and its results, the number of times evaluated and the
// number succeeded, are reported at the end of simulation, one line per
// statement after the $finish line, which is why a cover that never succeeds
// is here too.
//
// A statement label creates a named block around the assertion, and %m in a
// severity task inside it prints the hierarchical name with the label. The
// severity tasks print the same tool-specific message whether they stand in
// the pass or the fail statement, so the two $info lines assert_f prints on
// its two passes through the loop differ only in the user text.
//
// The clause's own example records $time into t on failure at 10 and delays
// the $error by 5: the message is printed at 15 and reads "assert failed at
// time 10". The fail statement is any procedural statement, so one here
// triggers an event another process waits on, and one sets a flag. And the
// execution of immediate assertions is controlled by the assertion control
// tasks of 20.11: an assertion under $assertoff runs neither statement, and
// one after $asserton runs its fail statement again.
//
// scripts/run_sim_tests compares standard output followed by standard error,
// so the three ERROR lines stand together at the end, in their own time
// order, after the cover results the end of simulation reports.
module immediate_assertions;
  logic [7:0] v;
  logic f;
  logic flag = 1'b0;
  int count = 0;
  time t;
  event failed;

  initial begin
    @(failed);
    $display("event: fail statement triggered failed at %0d", $time);
  end

  initial begin
    v = 8'd0;
    assert (v) $display("0 passes"); else $display("0 fails");
    v = 8'bx;
    assert (v) $display("x passes"); else $display("x fails");
    v = 8'bz;
    assert (v) $display("z passes"); else $display("z fails");
    v = 8'd2;
    assert (v) $display("2 passes"); else $display("2 fails");

    assert (v == 8'd2);
    assert (v == 8'd0) else $display("no pass statement: v is not 0");
    assert (v == 8'd0);
    assume (v == 8'd0) else $display("assume: v is not 0");
    cover_two: cover (v == 8'd2) $display("cover: v is 2");
    cover_never: cover (v == 8'd9) $display("cover: v is 9");

    for (int i = 1; i >= 0; i = i - 1) begin
      f = (i == 1);
      assert_f: assert (f) $info("passed in %m"); else $info("failed in %m");
    end

    #10 assert (v == 8'd0)
    else begin
      t = $time;
      #5 $error("assert failed at time %0t", t);
    end

    assert (v == 8'd0) count = count + 1; else -> failed;
    #1;
    assert (v == 8'd0) else flag = 1'b1;
    $display("flag after the fail statement is %0d", flag);

    $assertoff;
    assert (v == 8'd0) $display("checked while off: passed");
    else $display("checked while off: failed");
    $asserton;
    assert (v == 8'd0) $display("checked after on: passed");
    else $display("checked after on: failed");
    $finish;
  end
endmodule
