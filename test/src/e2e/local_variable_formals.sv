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
    #10 c = 1; data = 5;
    #10 c = 0; data = 9; a = 1;
    #10 a = 0; data_in = 3; do1 = 5;
    #10 b = 1; data_out = 8;
    #10 b = 0; do1 = 8;
    #10 do1 = 5; data = 5;
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
