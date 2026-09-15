// §16.11 Calling subroutines on match of a sequence: a task, void function
// or system task written in the list after a sequence, in parentheses with
// it, is called at every end point of the sequence, the calls of the list in
// order, scheduled in the Reactive region like an action block without the
// evaluation waiting on them; an argument passed by value reads the sampled
// value the match was evaluated with, and a local variable assigned before
// the call in the list may be passed by value. The clause's s1 and three
// sequences beside it run below, clk rising at 5, 15, 25, ... so that tick n
// is at 10n - 5, the tick counter counting straight through.
//
// s1 matches at the first b strictly after an a, and its $display writes v
// and w as assigned from e and f: a is high at tick 1 with e high and b at 3
// with f low, then a at 11 with e low and b at 12 with f high. every_end's
// $display runs at each end point of c ##[1:2] d, ticks 22 and 23 with c at
// 21 and d at 22 and 23. in_order's two calls run in the order written at
// the match of g at 31, the void function note after them. sampled's k
// counts the clock's edges through a nonblocking assignment, so at the tick
// at 41, h high, the match reads k as 40 where k reads 41 by the time the
// call runs in the Reactive region, which its argument passed by reference
// shows.
module subroutine_on_match;
  logic clk = 0;
  int tick = 1;
  int k = 0;
  logic a, b, c, d, e, f, g, h;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;
  always @(posedge clk) k <= k + 1;

  assign a = tick inside {1, 11};
  assign b = tick inside {3, 12};
  assign e = tick inside {1};
  assign f = tick inside {12};
  assign c = tick inside {21};
  assign d = tick inside {22, 23};
  assign g = tick inside {31};
  assign h = tick inside {41};

  function void note(int t);
    $display("note at tick %0d", t);
  endfunction

  function automatic void show(int by_value, ref int by_ref);
    $display("k by value = %0d, by reference = %0d", by_value, by_ref);
  endfunction

  sequence s1;
    logic v, w;
    @(posedge clk) (a, v = e) ##1
      (b[->1], w = f, $display("b after a with v = %h, w = %h", v, w));
  endsequence

  sequence every_end;
    @(posedge clk) (c ##[1:2] d, $display("c ##[1:2] d ends at tick %0d", tick));
  endsequence

  sequence in_order;
    @(posedge clk) (g, $display("first at tick %0d", tick),
                       $display("second at tick %0d", tick), note(tick));
  endsequence

  sequence sampled;
    @(posedge clk) (h, show(k, k));
  endsequence

  initial #450 $finish;
endmodule
