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
    #40;
    $display("a_plain passes %0d fails %0d", plain_pass, plain_fail);
    $display("a_rst passes %0d fails %0d", rst_pass, rst_fail);
    $display("a_live passes %0d fails %0d", live_pass, live_fail);
    $display("a_sampled passes %0d fails %0d", sampled_pass, sampled_fail);
    $display("a_guarded passes %0d fails %0d", guarded_pass, guarded_fail);
    $display("a_early passes %0d fails %0d", early_pass, early_fail);
    $finish;
  end
endmodule
