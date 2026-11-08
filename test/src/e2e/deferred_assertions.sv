module deferred_assertions;
  int v;
  int flag;
  int i;

  task automatic show(input string what, input int by_value, ref int by_ref);
    $display("%s: by value %0d, by reference %0d", what, by_value, by_ref);
  endtask

  function int twice(input int n);
    return n * 2;
  endfunction

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
    assert #0 (v == 1) show("observed", v, v); else note("observed: v was not 1");
    assert final (v == 1) show("final", v, v); else note("final: v was not 1");
    assert #0 (v == 1) show("observed twice", twice(v), v);
    assert #0 (v == 1) lg.say("a method call as the pass statement");
    v = 2;
    v <= 3;
    $display("active: v is %0d, and no deferred action has run yet", v);
    cover #0 (v == 2) write_v(20);
  end

  initial begin
    #10;
    flag = 0;
    assume #0 (flag == 1);
    for (i = 0; i < 3; i++)
      assert #0 (i < 2) note_index("observed pass at", i);
      else note_index("observed fail at", i);
    never: cover final (flag == 1) note("never: not reached");
    zero: cover #0 (flag == 0) note("zero: flag is 0");
    $display("active at 10: the loop's reports and the covers are pending");
    #1 $finish;
  end
endmodule
