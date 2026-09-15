// §16.5.1 Sampling: a concurrent assertion reads the sampled value of each
// variable, which at a time greater than 0 is the value the variable held in
// the Preponed region of the time slot and at time 0 is its default sampled
// value: the value assigned in a static variable's declaration, or the default
// of its type. A const cast's sampled value is the current value of its
// argument, an event's triggered is its current value, and a function called
// in the expression is applied to the sampled values of its arguments.
module sampled_values;
  // The time-zero tick: the initial block writes v and y before it raises
  // tick0, and the assertion still samples v's declared 5 and y's default x.
  int v = 5;
  logic y;
  logic tick0 = 0;
  t0_v: assert property (@(posedge tick0) v == 5)
    $display("t0_v: at time 0 v samples its declared 5 while v is now %0d", v);
  else
    $display("t0_v: failed");
  t0_y: assert property (@(posedge tick0) y === 1'bx)
    $display("t0_y: at time 0 y samples x while y is now %0d", y);
  else
    $display("t0_y: failed");

  initial begin
    v = 9;
    y = 1;
    tick0 = 1;
  end

  // The later ticks, at 5, 15, 25 and 35: a is written 1 in the time step of
  // the tick at 15 and 0 between the ticks at 25 and 35; e is triggered in the
  // time step of the tick at 25.
  logic clk = 0;
  logic a = 0;
  event e;
  always #5 clk = ~clk;

  function int twice(input int n);
    return 2 * n;
  endfunction

  // twice is applied to a's sampled value, the Preponed one, so the tick at
  // 15 reads 0 although a is 1 by the time the pass statement runs.
  pre: assert property (@(posedge clk) twice(a) == 0)
    $display("pre: sampled a is 0 at %0d, a is now %0d", $time, a);
  else
    $display("pre: sampled a is 1 at %0d, a is now %0d", $time, a);

  // const'(a) is a's current value, so at the tick at 15 it differs from the
  // sampled a.
  cc: assert property (@(posedge clk) const'(a) == a)
    $display("cc: const'(a) equals sampled a at %0d", $time);
  else
    $display("cc: const'(a) is %0d while sampled a differs at %0d", a, $time);

  // e.triggered is its current value, true through the time step e is
  // triggered in, so the tick at 25 covers it.
  ev: cover property (@(posedge clk) e.triggered)
    $display("ev: e.triggered is current at %0d", $time);

  initial begin
    #15 a = 1;
    #10 -> e;
    #7 a = 0;
    #12 $finish;
  end
endmodule
