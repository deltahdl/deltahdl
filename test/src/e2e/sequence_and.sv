// §16.9.5 AND operation: `s1 and s2` matches where both operand sequences
// match; the operands begin at the same tick, and where one matches first it
// waits for the other, the composite ending where the operand that completes
// last ends. With sampled expressions as operands, the composite matches at
// each tick both are true. The clause's examples are run below in three
// rounds of fourteen ticks, clk rising at 5, 15, 25, ... so that tick n of
// round r is at 10n - 5 + 140(r - 1), the tick counter counting straight
// through.
//
// Round one is Figure 16-5: te1 is high at ticks 1, 2 and 8, te2 at 10 and
// 12, te3 at 2, 3 and 8, te4 at 4 and 10 and te5 at 6 and 12. From tick 8,
// te1 ##2 te2 ends at 10 and te3 ##2 te4 ##2 te5 at 12, so their and ends at
// 12, the tick at 115; from tick 2 the second operand ends at 6 but the first
// does not match, so nothing ends there. te1 ##[1:5] te2 ends at 10 and 12
// from tick 8, and each of those combined with the second operand's 12 ends at
// 12, the tick at 115 again.
//
// Round two is Figure 16-6, ticks 15 to 28, with te2 high at 9 to 13 of the
// round instead: te1 ##[1:5] te2 has five matches from tick 8, ending at 9 to
// 13, four of which combine with the second operand's end at 12 to end at 12
// and the fifth to end at 13, the ticks at 255 and 265; te1 ##2 te2 ends at
// 10 alone, so its and ends at 12, the tick at 255.
//
// Round three is Figure 16-7, ticks 29 to 42, with te1 high at 1, 3, 8 and
// 14 of the round, te2 at 1, 3, 5, 8, 9 and 14 and te3, te4 and te5 low
// throughout: te1 and te2 matches at 1, 3, 8 and 14, the ticks at 285, 305,
// 355 and 415, and though te1 ##2 te2 matches from 1 and 3, the second
// operand of the composite sequences never does, so neither ends.
module sequence_and;
  logic clk = 0;
  int tick = 1;
  logic te1, te2, te3, te4, te5;
  string fixed_ends = "";
  string range_ends = "";
  string boolean_ends = "";
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign te1 = tick inside {1, 2, 8, 15, 16, 22, 29, 31, 36, 42};
  assign te2 = tick inside {10, 12, 23, 24, 25, 26, 27, 29, 31, 33, 36, 37, 42};
  assign te3 = tick inside {2, 3, 8, 16, 17, 22};
  assign te4 = tick inside {4, 10, 18, 24};
  assign te5 = tick inside {6, 12, 20, 26};

  sequence fixed_and;
    @(posedge clk) (te1 ##2 te2) and (te3 ##2 te4 ##2 te5);
  endsequence

  sequence range_and;
    @(posedge clk) (te1 ##[1:5] te2) and (te3 ##2 te4 ##2 te5);
  endsequence

  sequence boolean_and;
    @(posedge clk) te1 and te2;
  endsequence

  initial forever begin
    wait (fixed_and.triggered);
    fixed_ends = $sformatf("%s %0d", fixed_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (range_and.triggered);
    range_ends = $sformatf("%s %0d", range_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (boolean_and.triggered);
    boolean_ends = $sformatf("%s %0d", boolean_ends, $time);
    @(posedge clk);
  end

  initial begin
    #430;
    $display("(te1 ##2 te2) and (te3 ##2 te4 ##2 te5) ends at%s", fixed_ends);
    $display("(te1 ##[1:5] te2) and (te3 ##2 te4 ##2 te5) ends at%s",
             range_ends);
    $display("te1 and te2 ends at%s", boolean_ends);
    $finish;
  end
endmodule
