module property_instantiation;
  logic clk = 0;
  int tick = 1;
  logic sig, other, rst;
  int sig_pass = 0, sig_fail = 0;
  int other_pass = 0, other_fail = 0;
  int guarded_pass = 0, guarded_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign sig = tick inside {2, 3};
  assign other = tick inside {4};
  assign rst = tick inside {2};

  property p_low(x);
    @(posedge clk) !x;
  endproperty

  property p_guarded(x, r);
    @(posedge clk) disable iff (r) !x;
  endproperty

  low_sig: assert property (p_low(sig)) sig_pass++; else sig_fail++;
  low_other: assert property (p_low(other)) other_pass++; else other_fail++;
  guarded: assert property (p_guarded(sig, rst))
    guarded_pass++; else guarded_fail++;

  initial begin
    #40;
    $display("p_low(sig) passes %0d fails %0d", sig_pass, sig_fail);
    $display("p_low(other) passes %0d fails %0d", other_pass, other_fail);
    $display("p_guarded(sig, rst) passes %0d fails %0d", guarded_pass,
             guarded_fail);
    $finish;
  end
endmodule
