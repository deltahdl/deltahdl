module satisfaction_levels;
  logic clk = 0;
  int tick = 1;
  logic start, a, b, c;
  int strongly_pass = 0, strongly_fail = 0;
  int holds_pass = 0, holds_fail = 0;
  int pending_pass = 0, pending_fail = 0;
  int fails_pass = 0, fails_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign start = tick inside {1};
  assign a = 1;
  assign b = tick inside {2};
  assign c = 0;

  property hold_strongly;
    @(posedge clk) start |-> ##1 b;
  endproperty

  property hold;
    @(posedge clk) start |-> always a;
  endproperty

  property pend;
    @(posedge clk) start |-> s_eventually c;
  endproperty

  property fail;
    @(posedge clk) start |-> ##1 c;
  endproperty

  strongly: assert property (hold_strongly)
    strongly_pass++; else strongly_fail++;

  holds: assert property (hold)
    begin
      holds_pass++;
      if ($time == 80)
        $display("start |-> always a holds at the end of the run: no bad state seen, no obligation unmet, an extension may fail it");
    end else holds_fail++;

  pending: assert property (pend)
    pending_pass++;
    else begin
      pending_fail++;
      if ($time == 80)
        $display("start |-> s_eventually c is pending at the end of the run: no bad state seen, an obligation unmet");
    end

  fails: assert property (fail)
    fails_pass++; else fails_fail++;

  initial begin
    #80;
    $display("start |-> ##1 b passes %0d fails %0d at ticks, %0d in flight: holds strongly",
             strongly_pass, strongly_fail, 8 - strongly_pass - strongly_fail);
    $display("start |-> always a passes %0d fails %0d at ticks, %0d in flight",
             holds_pass, holds_fail, 8 - holds_pass - holds_fail);
    $display("start |-> s_eventually c passes %0d fails %0d at ticks, %0d in flight",
             pending_pass, pending_fail, 8 - pending_pass - pending_fail);
    $display("start |-> ##1 c passes %0d fails %0d at ticks, %0d in flight: fails",
             fails_pass, fails_fail, 8 - fails_pass - fails_fail);
    $finish;
  end
endmodule
