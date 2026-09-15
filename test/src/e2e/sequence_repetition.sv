// §16.9.2 Repetition in sequences: consecutive repetition `[*n]` or
// `[*min:max]` matches the operand at consecutive ticks and ends at the last
// of them, `[*]` and `[+]` standing for `[*0:$]` and `[*1:$]`; goto
// repetition `[->min:max]` matches a Boolean at ticks that need not be
// consecutive and ends at the last match; nonconsecutive repetition
// `[=min:max]` is the goto form extended past the last match by ticks the
// Boolean is false at. The clause's own sequences are run below. clk rises at
// 5, 15, 25, ...; a is high for the tick at 15, b for 25, 35 and 45, and c
// for 55 in the first round; in the second, from 105, a is high for 115, b
// for 125 and 135, and c for 155; in the third, from 205, a is high for 215,
// 245 and 275 and b for 235, 265 and 295; and in the fourth, from 305, a is
// high for 315 and b for 345, 355 and 365. Each process records the ticks its
// sequence ends at.
module sequence_repetition;
  logic clk = 0;
  logic a = 0;
  logic b = 0;
  logic c = 0;
  string three_ends = "";
  string plus_ends = "";
  string window_ends = "";
  string goto_ends = "";
  string noncons_ends = "";
  string delayed_ends = "";
  string group_ends = "";
  always #5 clk = ~clk;

  sequence three;
    @(posedge clk) a ##1 b[*3] ##1 c;
  endsequence

  sequence plus;
    @(posedge clk) a ##1 b[*1:$] ##1 c;
  endsequence

  sequence window;
    @(posedge clk) a[*0:3] ##1 b ##1 c;
  endsequence

  sequence goto_two;
    @(posedge clk) a ##1 b[->2:10] ##1 c;
  endsequence

  sequence noncons_two;
    @(posedge clk) a ##1 b[=2:10] ##1 c;
  endsequence

  sequence delayed;
    @(posedge clk) a ##3 (b[*3]);
  endsequence

  sequence group_three;
    @(posedge clk) (a ##2 b)[*3];
  endsequence

  initial forever begin
    wait (three.triggered);
    three_ends = $sformatf("%s %0d", three_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (plus.triggered);
    plus_ends = $sformatf("%s %0d", plus_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (window.triggered);
    window_ends = $sformatf("%s %0d", window_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (goto_two.triggered);
    goto_ends = $sformatf("%s %0d", goto_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (noncons_two.triggered);
    noncons_ends = $sformatf("%s %0d", noncons_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (delayed.triggered);
    delayed_ends = $sformatf("%s %0d", delayed_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (group_three.triggered);
    group_ends = $sformatf("%s %0d", group_ends, $time);
    @(posedge clk);
  end

  initial begin
    // Round one: a at 15, b at 25, 35 and 45, c at 55.
    #10 a = 1;
    #10 a = 0; b = 1;
    #30 b = 0; c = 1;
    #10 c = 0;
    // Round two, from 105: a at 115, b at 125 and 135, c at 155, with b low
    // at 145 between.
    #50 a = 1;
    #10 a = 0; b = 1;
    #20 b = 0;
    #10 c = 1;
    #10 c = 0;
    // Round three, from 205: a at 215, 245 and 275 and b at 235, 265 and 295.
    #50 a = 1;
    #10 a = 0;
    #10 b = 1;
    #10 b = 0; a = 1;
    #10 a = 0;
    #10 b = 1;
    #10 b = 0; a = 1;
    #10 a = 0;
    #10 b = 1;
    #10 b = 0;
    // Round four, from 305: a at 315 and b at 345, 355 and 365.
    #10 a = 1;
    #10 a = 0;
    #20 b = 1;
    #30 b = 0;
    #20;
    $display("a ##1 b[*3] ##1 c ends at%s", three_ends);
    $display("a ##1 b[*1:$] ##1 c ends at%s", plus_ends);
    $display("a[*0:3] ##1 b ##1 c ends at%s", window_ends);
    $display("a ##1 b[->2:10] ##1 c ends at%s", goto_ends);
    $display("a ##1 b[=2:10] ##1 c ends at%s", noncons_ends);
    $display("a ##3 (b[*3]) ends at%s", delayed_ends);
    $display("(a ##2 b)[*3] ends at%s", group_ends);
    $finish;
  end
endmodule
