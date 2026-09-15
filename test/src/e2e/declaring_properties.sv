// §16.12 Declaring properties: a named property declares a behaviour that
// an assert, assume or cover statement puts to use, with formal arguments an
// instance binds actual arguments to, the instance being the property's body
// with the actuals substituted for the formals, and instantiable before its
// declaration; a disable iff clause attached to a property_expr makes a
// property_spec whose attempts are disabled, neither succeeding nor failing,
// while the disable condition is true, the condition reading the variables'
// current values rather than sampled ones. The assertions below run over
// four ticks, clk rising at 5, 15, 25 and 35 so that tick n is at 10n - 5,
// the tick counter counting through: sig is high at ticks 2 and 3, rst at 2
// and 4, and live is set by a blocking assignment at the edge of tick 3 and
// cleared at the edge of tick 4. Each assertion counts its passes and
// failures, printed once at the end.
//
// a_plain, !sig, passes at 1 and 4 and fails at 2 and 3. a_rst, the same
// under disable iff (rst), is disabled at 2 and 4, so it passes at 1 and
// fails at 3. a_live, under disable iff (live), is disabled at 3 alone,
// live reading 1 there as the edge's assignment left it, so it passes at 1
// and 4 and fails at 2; a_sampled, !live, reads live's sampled value, 0 at
// 3 and 1 at 4, so it passes at 1 to 3 and fails at 4. a_guarded
// instantiates p_guarded(sig, rst), the assertion a_rst is, and a_early
// instantiates p_low(sig), declared after it, the assertion a_plain is.
module declaring_properties;
  logic clk = 0;
  int tick = 1;
  logic sig, rst;
  logic live = 0;
  int plain_pass = 0, plain_fail = 0;
  int rst_pass = 0, rst_fail = 0;
  int live_pass = 0, live_fail = 0;
  int sampled_pass = 0, sampled_fail = 0;
  int guarded_pass = 0, guarded_fail = 0;
  int early_pass = 0, early_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;
  always @(posedge clk) live = (tick == 3);

  assign sig = tick inside {2, 3};
  assign rst = tick inside {2, 4};

  a_early: assert property (p_low(sig)) early_pass++; else early_fail++;

  a_plain: assert property (@(posedge clk) !sig)
    plain_pass++; else plain_fail++;

  a_rst: assert property (@(posedge clk) disable iff (rst) !sig)
    rst_pass++; else rst_fail++;

  a_live: assert property (@(posedge clk) disable iff (live) !sig)
    live_pass++; else live_fail++;

  a_sampled: assert property (@(posedge clk) !live)
    sampled_pass++; else sampled_fail++;

  property p_guarded(x, r);
    @(posedge clk) disable iff (r) !x;
  endproperty

  a_guarded: assert property (p_guarded(sig, rst))
    guarded_pass++; else guarded_fail++;

  property p_low(x);
    @(posedge clk) !x;
  endproperty

  initial begin
    #50;
    $display("a_plain passes %0d fails %0d", plain_pass, plain_fail);
    $display("a_rst passes %0d fails %0d", rst_pass, rst_fail);
    $display("a_live passes %0d fails %0d", live_pass, live_fail);
    $display("a_sampled passes %0d fails %0d", sampled_pass, sampled_fail);
    $display("a_guarded passes %0d fails %0d", guarded_pass, guarded_fail);
    $display("a_early passes %0d fails %0d", early_pass, early_fail);
    $finish;
  end
endmodule
