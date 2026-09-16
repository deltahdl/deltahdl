// §16.12.21 Finite-length versus infinite-length behavior: dynamic
// verification considers behaviours of finite length alone, on which a
// property is satisfied at one of four levels. It holds strongly where no
// bad state has been seen, every future obligation has been met and it
// holds on any extension of the path; it holds, but not strongly, where no
// bad state has been seen and every obligation has been met but an
// extension may fail it; it is pending where no bad state has been seen
// but an obligation has not been met; and it fails where a bad state has
// been seen, so that it holds on no extension. The assertions below run
// over eight ticks, clk rising at 5, 15, ..., 75 so that tick n is at 10n -
// 5, the run ending at 80: start is high at 1 alone, a throughout, b at 2
// alone and c never, and each property is start |-> p, so that the attempt
// from 1 is the one p is put to and the seven others hold at their tick
// with start low.
//
// strongly, start |-> ##1 b, is decided true at 2, where b holds: no
// extension of the path can fail it, so it holds strongly, and every
// attempt is decided before the run ends. holds, start |-> always a, sees
// no bad state and, always being weak, has no obligation unmet when the
// run ends, but a could fall on an extension, so it holds without holding
// strongly, its verdict reached at the end of the run. pending, start |->
// s_eventually c, sees no bad state either, but s_eventually is strong and
// c has not happened when the run ends, an obligation unmet, so it is
// pending, which the end of the run reports as its attempt failing. fails,
// start |-> ##1 c, sees a bad state at 2, where c is low, and fails there.
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
