// §16.5.2 Assertion clock: the clock of a concurrent assertion is whatever
// event expression the user writes, and it can differ from one assertion to
// the next. A variable that appears in both the clock expression and the
// assertion's expression is read twice over: the clock reads its current
// value while the assertion reads its sampled value, so clk itself samples 0
// at its own rising edge. A gated clock, clk iff gate, ticks only while the
// gate is high. $global_clock refers to the clocking event of the global
// clocking declaration and clocks an assertion as @(posedge clk) does. The
// clause's own example prints %m from its action block, which names the
// assertion. As Figure 16-1 has it, req rising in the time step of a tick is
// sampled low at that tick and high at the next.
module assertion_clock;
  logic clk = 0;
  logic gate = 1;
  logic req = 0;
  always #5 clk = ~clk;
  global clocking gclk @(posedge clk); endclocking

  clk_low: assert property (@(posedge clk) clk == 0)
    $display("clk_low: sampled clk is 0 at %0d while clk reads %0d", $time, clk);
  else
    $display("clk_low: failed at %0d", $time);

  gated: assert property (@(posedge clk iff gate) 1'b1)
    $display("gated: tick at %0d", $time);

  gl: assert property (@$global_clock req)
    $display("gl: req sampled high at %0d", $time);
  else
    $display("gl: req sampled low at %0d", $time);

  base_rule1: assert property (@(posedge clk) req)
    $display("%m, passing");
  else
    $display("%m, failed");

  initial begin
    #25 req = 1;
    #5 gate = 0;
    #20 gate = 1;
    #7 $finish;
  end
endmodule
