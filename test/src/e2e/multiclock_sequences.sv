module multiclock_sequences;
  logic clk0 = 0;
  logic clk1 = 0;
  int tick = 1;
  logic sig0, sig1;
  int delayed_pass = 0, delayed_fail = 0;
  int overlapped_pass = 0, overlapped_fail = 0;
  int same_pass = 0, same_fail = 0;
  int plain_pass = 0, plain_fail = 0;
  string delayed_at = "", overlapped_at = "", same_at = "", plain_at = "";
  always #5 clk0 = ~clk0;
  always #10 tick = tick + 1;
  initial begin
    #12 clk1 = 1;
    #8 clk1 = 0;
    #7 clk1 = 1;
    #8 clk1 = 0;
    #10 clk1 = 1;
    #5 clk1 = 0;
    #7 clk1 = 1;
    #8 clk1 = 0;
    #7 clk1 = 1;
    #6 clk1 = 0;
  end

  assign sig0 = tick inside {1, 2, 5, 7};
  assign sig1 = tick inside {3, 5};

  delayed: assert property (@(posedge clk0) sig0 ##1 @(posedge clk1) sig1)
    begin
      delayed_pass++;
      delayed_at = $sformatf("%s %0d", delayed_at, $time);
    end else delayed_fail++;

  overlapped: assert property (@(posedge clk0) sig0 ##0 @(posedge clk1) sig1)
    begin
      overlapped_pass++;
      overlapped_at = $sformatf("%s %0d", overlapped_at, $time);
    end else overlapped_fail++;

  same_clock: assert property (@(posedge clk0) sig0 ##1 @(posedge clk0) sig1)
    begin
      same_pass++;
      same_at = $sformatf("%s %0d", same_at, $time);
    end else same_fail++;

  plain: assert property (@(posedge clk0) sig0 ##1 sig1)
    begin
      plain_pass++;
      plain_at = $sformatf("%s %0d", plain_at, $time);
    end else plain_fail++;

  initial begin
    #80;
    $display("sig0 ##1 @(posedge clk1) sig1 passes %0d fails %0d, passing at%s",
             delayed_pass, delayed_fail, delayed_at);
    $display("sig0 ##0 @(posedge clk1) sig1 passes %0d fails %0d, passing at%s",
             overlapped_pass, overlapped_fail, overlapped_at);
    $display("sig0 ##1 @(posedge clk0) sig1 passes %0d fails %0d, passing at%s",
             same_pass, same_fail, same_at);
    $display("sig0 ##1 sig1 passes %0d fails %0d, passing at%s", plain_pass,
             plain_fail, plain_at);
    $finish;
  end
endmodule
