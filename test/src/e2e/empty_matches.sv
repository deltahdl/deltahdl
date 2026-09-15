// §16.9.2.1 Repetition, concatenation, and empty matches: a repetition count
// of 0 gives an empty sequence, and concatenation with one follows the
// clause's rules: `empty ##0 seq` and `seq ##0 empty` match nowhere, `empty
// ##n seq` is `##(n-1) seq` and `seq ##n empty` is `seq ##(n-1) `true`. So
// `a[*0] ##0 b` never ends where the fusion ``true ##0 b` ends at every tick
// b holds at, `b ##2 a[*0]` ends a tick after each b, and a sequence
// admitting both an empty and a nonempty match is the or of its cases,
// `b ##1 a[*0:1] ##2 c` being `(b ##2 c) or (b ##1 a ##2 c)`. clk rises at 5,
// 15, 25, ...; b is high for the ticks at 15 and 25 and a for the tick at 25;
// then b is high for 55 and c for 75, and b for 95, a for 105 and c for 125.
module empty_matches;
  logic clk = 0;
  logic a = 0;
  logic b = 0;
  logic c = 0;
  string never_ends = "";
  string fused_ends = "";
  string trailing_ends = "";
  string cases_ends = "";
  string spelled_ends = "";
  always #5 clk = ~clk;

  sequence never;
    @(posedge clk) a[*0] ##0 b;
  endsequence

  sequence fused;
    @(posedge clk) 1'b1 ##0 b;
  endsequence

  sequence trailing;
    @(posedge clk) b ##2 a[*0];
  endsequence

  sequence cases;
    @(posedge clk) b ##1 a[*0:1] ##2 c;
  endsequence

  sequence spelled;
    @(posedge clk) b ##2 c or b ##1 a ##2 c;
  endsequence

  initial forever begin
    wait (never.triggered);
    never_ends = $sformatf("%s %0d", never_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (fused.triggered);
    fused_ends = $sformatf("%s %0d", fused_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (trailing.triggered);
    trailing_ends = $sformatf("%s %0d", trailing_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (cases.triggered);
    cases_ends = $sformatf("%s %0d", cases_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (spelled.triggered);
    spelled_ends = $sformatf("%s %0d", spelled_ends, $time);
    @(posedge clk);
  end

  initial begin
    #10 b = 1;
    #10 a = 1;
    #10 a = 0; b = 0;
    #20 b = 1;
    #10 b = 0;
    #10 c = 1;
    #10 c = 0;
    #10 b = 1;
    #10 b = 0; a = 1;
    #10 a = 0;
    #10 c = 1;
    #10 c = 0;
    #20;
    $display("a[*0] ##0 b ends at%s", never_ends);
    $display("`true ##0 b ends at%s", fused_ends);
    $display("b ##2 a[*0] ends at%s", trailing_ends);
    $display("b ##1 a[*0:1] ##2 c ends at%s", cases_ends);
    $display("(b ##2 c) or (b ##1 a ##2 c) ends at%s", spelled_ends);
    $finish;
  end
endmodule
