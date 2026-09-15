// §16.9.1 Operator precedence: Table 16-1 orders the sequence operators, ##
// binding tighter than and and and tighter than or, the two associating to
// the left. Three sequences over the same four signals read by that order:
// concat_and is `(a ##1 b) and c`, both operands matched from the tick at 15
// where a and c hold and the whole ending at the later end point, 25 where b
// holds; and_or is `(a and c) or d`, ending at 15 where a and c both hold and
// at 25, 45 and 55 where d holds; and concat_or is `(a ##1 b) or (c ##1 d)`,
// ending at 25 where the first concatenation does, and at 55 where c at 45 is
// followed by d. clk rises at 5, 15, 25, ...
module sequence_operator_precedence;
  logic clk = 0;
  logic a = 0;
  logic b = 0;
  logic c = 0;
  logic d = 0;
  string concat_and_ends = "";
  string and_or_ends = "";
  string concat_or_ends = "";
  always #5 clk = ~clk;

  sequence concat_and;
    @(posedge clk) a ##1 b and c;
  endsequence

  sequence and_or;
    @(posedge clk) a and c or d;
  endsequence

  sequence concat_or;
    @(posedge clk) a ##1 b or c ##1 d;
  endsequence

  initial forever begin
    wait (concat_and.triggered);
    concat_and_ends = $sformatf("%s %0d", concat_and_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (and_or.triggered);
    and_or_ends = $sformatf("%s %0d", and_or_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (concat_or.triggered);
    concat_or_ends = $sformatf("%s %0d", concat_or_ends, $time);
    @(posedge clk);
  end

  initial begin
    #10 a = 1; c = 1;
    #10 a = 0; c = 0; b = 1; d = 1;
    #10 b = 0; d = 0;
    #10 c = 1; d = 1;
    #10 c = 0;
    #10 d = 0;
    #20;
    $display("a ##1 b and c ends at%s", concat_and_ends);
    $display("a and c or d ends at%s", and_or_ends);
    $display("a ##1 b or c ##1 d ends at%s", concat_or_ends);
    $finish;
  end
endmodule
