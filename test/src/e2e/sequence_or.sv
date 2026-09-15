// §16.9.7 OR operation: `s1 or s2` matches where at least one operand
// sequence matches, and its matches are the union of the operands' matches,
// each ending where the operand's match ends; with sampled expressions as
// operands, it matches at each tick at least one of them is true. The
// clause's figures are run below in two rounds of fourteen ticks, clk rising
// at 5, 15, 25, ... so that tick n is at 10n - 5, the tick counter counting
// straight through, and each process records the ticks its sequence reaches
// an end point at.
//
// Round one, ticks 1 to 14, is Figures 16-10 and 16-11 at once: te1 is high
// at ticks 1, 2 and 8, te2 at 9 to 13, te3 at 2, 3 and 8, te4 at 10 and te5
// at 12. From tick 8, te1 ##2 te2 ends at 10 and te3 ##2 te4 ##2 te5 at 12,
// so (te1 ##2 te2) or (te3 ##2 te4 ##2 te5) ends at 10 and 12; te1 ##[1:5]
// te2 ends at 9 to 13, so (te1 ##[1:5] te2) or (te3 ##2 te4 ##2 te5) ends at
// each tick from 9 to 13, twice at 12; and te1 or te2 ends at 1, 2 and 8 and
// 9 to 13. From ticks 1 and 2 te2 is low through the five ticks after, and
// from 2 and 3 te4 is low two ticks on, so no other attempt ends.
//
// Round two, ticks 15 to 28, is Figure 16-9: te1 is high at 1, 3, 6, 8, 11,
// 12 and 14 of the round and te2 at 1, 2, 4, 5, 8, 9, 10 and 14, te3 to te5
// low throughout, so te1 or te2 ends at every tick of the round but 7 and
// 13, which are 21 and 27. The sequences keep matching there through te1
// ##2 te2, which ends two ticks after te1 at 3, 6, 8 and 12 of the round,
// 19, 22, 24 and 28, and through te1 ##[1:5] te2, which ends at each tick
// te2 is high at within five of a te1: 16, 18, 19, 22, 23, 24 and 28.
module sequence_or;
  logic clk = 0;
  int tick = 1;
  logic te1, te2, te3, te4, te5;
  string fixed_ends = "";
  string range_ends = "";
  string either_ends = "";
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign te1 = tick inside {1, 2, 8, 15, 17, 20, 22, 25, 26, 28};
  assign te2 = tick inside {9, 10, 11, 12, 13, 15, 16, 18, 19, 22, 23, 24, 28};
  assign te3 = tick inside {2, 3, 8};
  assign te4 = tick inside {10};
  assign te5 = tick inside {12};

  sequence fixed_or;
    @(posedge clk) (te1 ##2 te2) or (te3 ##2 te4 ##2 te5);
  endsequence

  sequence range_or;
    @(posedge clk) (te1 ##[1:5] te2) or (te3 ##2 te4 ##2 te5);
  endsequence

  sequence either;
    @(posedge clk) te1 or te2;
  endsequence

  initial forever begin
    wait (fixed_or.triggered);
    fixed_ends = $sformatf("%s %0d", fixed_ends, tick);
    @(posedge clk);
  end
  initial forever begin
    wait (range_or.triggered);
    range_ends = $sformatf("%s %0d", range_ends, tick);
    @(posedge clk);
  end
  initial forever begin
    wait (either.triggered);
    either_ends = $sformatf("%s %0d", either_ends, tick);
    @(posedge clk);
  end

  initial begin
    #290;
    $display("(te1 ##2 te2) or (te3 ##2 te4 ##2 te5) ends at ticks%s",
             fixed_ends);
    $display("(te1 ##[1:5] te2) or (te3 ##2 te4 ##2 te5) ends at ticks%s",
             range_ends);
    $display("te1 or te2 ends at ticks%s", either_ends);
    $finish;
  end
endmodule
