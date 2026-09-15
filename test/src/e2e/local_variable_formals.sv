// §16.8.2 Local variable formal arguments in sequence declarations: a formal
// designated local is a local variable of the sequence, a new copy of it made
// at the beginning of each attempt of an instance; one of direction input or
// inout is initialized from the actual before the instance's first operand,
// and one of direction inout or output is assigned back to the actual's local
// variable when the instance matches. The clause's sub_seq2 and seq2 are run
// here with the repetition in sub_seq2 left out: seq2 captures data into v1,
// hands v1 to sub_seq2's inout lv, which adds data_in to it, and reads v1
// back as lv where the instance matched. Two rounds are driven, the second
// with data_out not equal to lv so that sub_seq2 does not match and nothing is
// assigned back. clk rises at 5, 15, 25, ...
module local_variable_formals;
  logic clk = 0;
  logic c = 0;
  logic a = 0;
  logic b = 0;
  int data = 0;
  int data_in = 0;
  int data_out = 0;
  int do1 = 0;
  string seq2_ends = "";
  string in_ends = "";
  always #5 clk = ~clk;

  sequence sub_seq2(local inout int lv);
    (a ##1 !a, lv += data_in) ##1 b && (data_out == lv);
  endsequence

  sequence seq2;
    int v1;
    @(posedge clk) (c, v1 = data) ##1 sub_seq2(v1) ##1 (do1 == v1);
  endsequence

  // An input local formal keeps the value its actual had when the attempt
  // began: sub_in(data) compares do1 two ticks after c's tick with data as
  // it stood at c's tick, 5, though data reads 9 by then in the first round.
  sequence sub_in(local input int lv);
    c ##2 (do1 == lv);
  endsequence

  sequence in_inst;
    @(posedge clk) sub_in(data);
  endsequence

  initial forever begin
    wait (seq2.triggered);
    seq2_ends = $sformatf("%s %0d", seq2_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (in_inst.triggered);
    in_ends = $sformatf("%s %0d", in_ends, $time);
    @(posedge clk);
  end

  initial begin
    // Round one: v1 captures 5 at 15, lv is 5 at 25 and 8 at 35, data_out
    // is 8 at 45 so sub_seq2 matches and v1 becomes 8, and do1 is 8 at 55;
    // do1 is 5 at 35, where sub_in's attempt from 15 reads its lv.
    #10 c = 1; data = 5;
    #10 c = 0; data = 9; a = 1;
    #10 a = 0; data_in = 3; do1 = 5;
    #10 b = 1; data_out = 8;
    #10 b = 0; do1 = 8;
    #10 do1 = 5; data = 5;
    // Round two: the same but for data_out, 7 against lv's 8 at 105, so
    // sub_seq2 does not match and seq2 does not end though do1 is 8 at 115;
    // sub_in's attempt from 75 reads do1 as 5 at 95.
    #10 c = 1;
    #10 c = 0; a = 1;
    #10 a = 0;
    #10 b = 1; data_out = 7;
    #10 b = 0; do1 = 8;
    #10 do1 = 0;
    #20;
    $display("seq2, v1 read back from sub_seq2's lv, ends at%s", seq2_ends);
    $display("sub_in(data), lv initialized at the attempt, ends at%s", in_ends);
    $finish;
  end
endmodule
