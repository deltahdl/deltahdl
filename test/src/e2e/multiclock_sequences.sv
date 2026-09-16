// §16.13 Multiclock support: a sequence may be built from subsequences on
// different clocks, joined by ##1, which moves from the end point of the
// first, at a tick of its clock, to the nearest strictly subsequent tick of
// the second clock, or by ##0, which moves to the nearest possibly
// overlapping tick of the second clock, the same tick where the two clocks
// tick together; and where the two clocks are identical the sequence is the
// singly clocked one. clk0 rises at 5, 15, ..., 75 so that tick n of it is
// at 10n - 5, the tick counter counting through, and clk1 rises at 12, 27,
// 45, 57 and 72, reading the counter as 2, 3, 5, 6 and 8, the tick at 45
// together with clk0's fifth: sig0 is high at 1, 2, 5 and 7 and sig1 at 3
// and 5.
//
// delayed, sig0 ##1 @(posedge clk1) sig1, begins at each tick of clk0 and,
// sig0 holding, reads sig1 at the next tick of clk1 after it: the attempt
// from 15 holds at 27, the one from 45 fails at 57, the next tick of clk1
// strictly after 45, and those from 5 and 65 fail at 12 and 72; the four
// with sig0 low fail at their tick. overlapped, with ##0, is the same but
// for the attempt from 45, which reads sig1 at clk1's tick at 45 itself
// and holds there. same_clock names clk0 again after ##1, which changes
// nothing, so it reads as plain, sig0 ##1 sig1, does: sig1 a tick of clk0
// after sig0, which holds from 15 alone, at 25.
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
