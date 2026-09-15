// §16.8 Declaring sequences: a named sequence is declared with an optional
// list of formal arguments and instantiated by its name, the actuals bound to
// the formals by position or by name and substituted for the formals'
// references, `$` among them as the upper bound of a delay range; an instance
// stands anywhere a sequence_expr does, before the declaration included, and
// behaves as the flattened sequence; a sequence declared without a clock
// inherits one from the sequence that instantiates it; and a sequence is
// evaluated on the clocking event it names, posedge, negedge or either edge.
// The clause's own s, rule and s20_1 are run here beside a windowed one. clk
// rises at 5, 15, 25, ... and falls at 10, 20, 30, ...; each signal is high
// for one tick, and each process records the ticks its sequence ends at.
module named_sequences;
  logic clk = 0;
  logic trans = 0;
  logic start_trans = 0;
  logic a = 0;
  logic b = 0;
  logic c = 0;
  logic end_trans = 0;
  logic frame = 0;
  logic [7:0] data_bus = 0;
  logic [3:0] c_be = 0;
  logic g = 0;
  logic h = 0;
  logic j = 0;
  logic k = 0;
  string rule_ends = "";
  string s20_ends = "";
  string win_ends = "";
  string win_named_ends = "";
  string s3_ends = "";
  string s4_ends = "";
  always #5 clk = ~clk;

  sequence s;
    a ##1 b ##1 c;
  endsequence

  sequence rule;
    @(posedge clk) trans ##1 start_trans ##1 s ##1 end_trans;
  endsequence

  sequence s20_1(data, en);
    (!frame && (data == data_bus)) ##1 (c_be[3:0] == en);
  endsequence

  sequence s20_inst;
    @(posedge clk) s20_1(8'h5a, 4'hf);
  endsequence

  sequence win(x, y, lo, hi);
    x ##[lo:hi] y;
  endsequence

  sequence win_pos;
    @(posedge clk) win(a, c, 2, $);
  endsequence

  sequence win_named;
    @(posedge clk) win(.hi(2), .lo(1), .y(b), .x(a));
  endsequence

  sequence s3;
    @(negedge clk) g ##1 h;
  endsequence

  sequence s4;
    @(edge clk) j ##1 k;
  endsequence

  initial forever begin
    wait (rule.triggered);
    rule_ends = $sformatf("%s %0d", rule_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (s20_inst.triggered);
    s20_ends = $sformatf("%s %0d", s20_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (win_pos.triggered);
    win_ends = $sformatf("%s %0d", win_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (win_named.triggered);
    win_named_ends = $sformatf("%s %0d", win_named_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (s3.triggered);
    s3_ends = $sformatf("%s %0d", s3_ends, $time);
    @(negedge clk);
  end
  initial forever begin
    wait (s4.triggered);
    s4_ends = $sformatf("%s %0d", s4_ends, $time);
    @(edge clk);
  end

  initial begin #10 trans = 1; #10 trans = 0; end
  initial begin #20 start_trans = 1; #10 start_trans = 0; end
  initial begin #30 a = 1; #10 a = 0; end
  initial begin #40 b = 1; #10 b = 0; end
  initial begin #50 c = 1; #10 c = 0; end
  initial begin #60 end_trans = 1; #10 end_trans = 0; end
  initial begin #70 data_bus = 8'h5a; #10 data_bus = 0; end
  initial begin #80 c_be = 4'hf; #10 c_be = 0; end
  initial begin #25 g = 1; #10 g = 0; end
  initial begin #35 h = 1; #10 h = 0; end
  initial begin #42 j = 1; #6 j = 0; end
  initial begin #48 k = 1; #4 k = 0; end

  initial begin
    #100;
    $display("rule, trans ##1 start_trans ##1 s ##1 end_trans, ends at%s", rule_ends);
    $display("s20_1(8'h5a, 4'hf) ends at%s", s20_ends);
    $display("win(a, c, 2, $), a ##[2:$] c, ends at%s", win_ends);
    $display("win(.hi(2), .lo(1), .y(b), .x(a)), a ##[1:2] b, ends at%s", win_named_ends);
    $display("s3 on negedge clk ends at%s", s3_ends);
    $display("s4 on edge clk ends at%s", s4_ends);
    $finish;
  end
endmodule
