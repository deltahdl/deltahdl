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
    #10 a = 1;
    #10 a = 0; b = 1;
    #30 b = 0; c = 1;
    #10 c = 0;
    #50 a = 1;
    #10 a = 0; b = 1;
    #20 b = 0;
    #10 c = 1;
    #10 c = 0;
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
