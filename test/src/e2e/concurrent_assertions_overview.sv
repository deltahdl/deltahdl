// §16.5 Concurrent assertions overview: a concurrent assertion is evaluated
// only at the ticks of its clock, over the sampled values of its expression,
// and in the Observed region. clk rises at 5, 15, 25, 35 and 45; a pulses
// between the first two ticks and is never seen; a is written 1 in the same
// time step as the third tick, so that tick samples the value a held before
// the step, 0, and the assertion passes while a already reads 1 in its pass
// statement, which runs in the Reactive region after the tick's own display;
// the fourth tick samples the 1 and fails; a falls between the ticks after,
// and the fifth passes.
module concurrent_assertions_overview;
  logic clk = 0;
  logic a = 0;
  int ticks = 0;

  always #5 clk = ~clk;

  always @(posedge clk) begin
    ticks = ticks + 1;
    $display("tick %0d at %0d", ticks, $time);
  end

  a_low: assert property (@(posedge clk) !a)
    $display("a_low: passed at %0d, a is now %0d", $time, a);
  else
    $display("a_low: failed at %0d, a is now %0d", $time, a);

  initial begin
    #7 a = 1;
    #3 a = 0;
    #15 a = 1;
    #12 a = 0;
    #13 $finish;
  end
endmodule
