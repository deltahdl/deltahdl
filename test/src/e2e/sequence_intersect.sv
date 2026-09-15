// §16.9.6 Intersection: `s1 intersect s2` matches where both operand
// sequences match and the two matches have the same length, which is what
// tells it from `and`; an attempt's matches of the first operand are paired
// with those of the second of the same length, each pair a match of the
// composite with that length and end point, and where no pair exists the
// composite has no match. The sequences below run through three rounds of
// fourteen ticks, clk rising at 5, 15, 25, ... so that tick n of round r is
// at 10n - 5 + 140(r - 1), the tick counter counting straight through; te1
// is high at ticks 1, 2 and 8 of every round, te3 at 2, 3 and 8, te4 at 4
// and 10, and te5 at 6 and 12.
//
// Round one is Figure 16-8, with te2 high at ticks 9 to 13: from tick 8,
// te1 ##[1:5] te2 has five matches, ending at 9 to 13, and te3 ##2 te4 ##2
// te5 one, ending at 12, so their intersection has the one match of the pair
// of four-tick matches, ending at 12, the tick at 115, where their and,
// beside it, ends at 12 and at 13.
//
// Round two, ticks 15 to 28, has te2 high at 10 and 12 of the round and te5
// at 6, 10 and 12: te1 ##[1:5] te2 ends at 10 and 12, and te3 ##2 te4
// ##[0:2] te5 at 10 and 12 as well, so the intersection of the two has two
// matches, of two and of four ticks, ending at the ticks at 235 and 255; the
// intersection with te3 ##2 te4 ##2 te5, ending at 12 alone, pairs the
// four-tick matches and ends at 255, as does the and.
//
// Round three, ticks 29 to 42, has te2 high at 10 of the round alone: te1
// ##[1:5] te2 ends at 10, two ticks long, and both second operands end at
// 12, four ticks long, so though every operand matches neither intersection
// does, where the and ends at 12, the tick at 395.
module sequence_intersect;
  logic clk = 0;
  int tick = 1;
  logic te1, te2, te3, te4, te5;
  string intersect_ends = "";
  string and_ends = "";
  string pairs_ends = "";
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign te1 = tick inside {1, 2, 8, 15, 16, 22, 29, 30, 36};
  assign te2 = tick inside {9, 10, 11, 12, 13, 24, 26, 38};
  assign te3 = tick inside {2, 3, 8, 16, 17, 22, 30, 31, 36};
  assign te4 = tick inside {4, 10, 18, 24, 32, 38};
  assign te5 = tick inside {6, 12, 20, 24, 26, 34, 40};

  sequence same_length;
    @(posedge clk) (te1 ##[1:5] te2) intersect (te3 ##2 te4 ##2 te5);
  endsequence

  sequence any_length;
    @(posedge clk) (te1 ##[1:5] te2) and (te3 ##2 te4 ##2 te5);
  endsequence

  sequence pairs;
    @(posedge clk) (te1 ##[1:5] te2) intersect (te3 ##2 te4 ##[0:2] te5);
  endsequence

  initial forever begin
    wait (same_length.triggered);
    intersect_ends = $sformatf("%s %0d", intersect_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (any_length.triggered);
    and_ends = $sformatf("%s %0d", and_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (pairs.triggered);
    pairs_ends = $sformatf("%s %0d", pairs_ends, $time);
    @(posedge clk);
  end

  initial begin
    #430;
    $display("(te1 ##[1:5] te2) intersect (te3 ##2 te4 ##2 te5) ends at%s",
             intersect_ends);
    $display("(te1 ##[1:5] te2) and (te3 ##2 te4 ##2 te5) ends at%s",
             and_ends);
    $display("(te1 ##[1:5] te2) intersect (te3 ##2 te4 ##[0:2] te5) ends at%s",
             pairs_ends);
    $finish;
  end
endmodule
