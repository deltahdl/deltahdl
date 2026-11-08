module assertion_clock;
  logic clk = 0;
  logic gate = 1;
  logic req = 0;
  int clk_sampled_low = 0;
  int clk_sampled_high = 0;
  int gated_ticks = 0;
  int gl_high = 0;
  int gl_low = 0;
  always #5 clk = ~clk;
  global clocking gclk @(posedge clk); endclocking

  clk_low: assert property (@(posedge clk) clk == 0)
    clk_sampled_low = clk_sampled_low + 1;
  else
    clk_sampled_high = clk_sampled_high + 1;

  gated: assert property (@(posedge clk iff gate) 1'b1)
    gated_ticks = gated_ticks + 1;

  gl: assert property (@$global_clock req)
    gl_high = gl_high + 1;
  else
    gl_low = gl_low + 1;

  base_rule1: assert property (@(posedge clk) req)
    $display("%m, passing");
  else
    $display("%m, failed");

  initial begin
    #25 req = 1;
    #5 gate = 0;
    #20 gate = 1;
    #7;
    $display("clk_low: sampled clk was 0 at %0d ticks and 1 at %0d", clk_sampled_low, clk_sampled_high);
    $display("gated: %0d of the 6 ticks had the gate high", gated_ticks);
    $display("gl: req sampled high at %0d ticks and low at %0d", gl_high, gl_low);
    $finish;
  end
endmodule
