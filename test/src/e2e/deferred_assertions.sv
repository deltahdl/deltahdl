// §16.4 Deferred assertions: an immediate assertion written with #0 (observed)
// or final after assert, assume or cover. Its expression is evaluated where the
// statement is processed, as any immediate assertion's is, but the report is
// deferred: the action block, which is a single subroutine call, runs in the
// Reactive region for the observed form and in the Postponed region for the
// final form. An actual passed by value, a function call included, is evaluated
// at the instant the expression is; an actual passed by reference reads the
// value its variable holds when the call runs in its region. A deferred assume
// and a deferred cover behave as the simple immediate forms of §16.3 apart from
// the deferral, so a failing assume with no else draws the default $error, and
// a cover's results are reported at the end of simulation.
module deferred_assertions;
  int v;
  int flag;
  int i;

  // §13.5.2: a ref formal needs an automatic subroutine.
  task automatic show(input string what, input int by_value, ref int by_ref);
    $display("%s: by value %0d, by reference %0d", what, by_value, by_ref);
  endtask

  function int twice(input int n);
    return n * 2;
  endfunction

  // An observed action runs in the Reactive region, where a variable may be
  // written; a final action's subroutine may not write one (§4.4.2.9).
  function void write_v(input int n);
    v = n;
    $display("write_v in the Reactive region: v is now %0d", v);
  endfunction

  task automatic note(input string what);
    $display("%s", what);
  endtask

  task automatic note_index(input string what, input int n);
    $display("%s %0d", what, n);
  endtask

  class Log;
    function void say(input string what);
      $display("Log.say: %s", what);
    endfunction
  endclass

  Log lg = new();

  initial begin
    v = 1;
    // The observed action runs in the Reactive region, after the Active
    // statements below and after the NBA to v; the final action runs in the
    // Postponed region, after every observed one.
    assert #0 (v == 1) show("observed", v, v); else note("observed: v was not 1");
    assert final (v == 1) show("final", v, v); else note("final: v was not 1");
    // The by-value actual twice(v) is evaluated now, with v at 1.
    assert #0 (v == 1) show("observed twice", twice(v), v);
    // A void function method is a permitted single subroutine call.
    assert #0 (v == 1) lg.say("a method call as the pass statement");
    v = 2;
    v <= 3;
    $display("active: v is %0d, and no deferred action has run yet", v);
    // This observed cover's action writes v in the Reactive region, after the
    // three observed reports above, so the final report reads 20 by reference.
    cover #0 (v == 2) write_v(20);
  end

  initial begin
    #10;
    flag = 0;
    // A deferred assume failing with no else draws the default $error, in the
    // Reactive region rather than where the statement is processed.
    assume #0 (flag == 1);
    // One statement processed three times queues three reports, each carrying
    // the counter as it stood when that pass evaluated the expression.
    for (i = 0; i < 3; i++)
      assert #0 (i < 2) note_index("observed pass at", i);
      else note_index("observed fail at", i);
    never: cover final (flag == 1) note("never: not reached");
    zero: cover #0 (flag == 0) note("zero: flag is 0");
    $display("active at 10: the loop's reports and the covers are pending");
    #1 $finish;
  end
endmodule
