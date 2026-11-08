module sequence_operations;
  logic clk = 0;
  logic a = 0;
  logic b = 0;
  logic c = 0;
  logic d = 0;
  string with_or_ends = "";
  string either_ends = "";
  always #5 clk = ~clk;

  sequence with_or;
    @(posedge clk) a ##1 b or c ##1 d;
  endsequence

  sequence either;
    @(posedge clk) a or c;
  endsequence

  initial forever begin
    wait (with_or.triggered);
    with_or_ends = $sformatf("%s %0d", with_or_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (either.triggered);
    either_ends = $sformatf("%s %0d", either_ends, $time);
    @(posedge clk);
  end

  initial begin
    #10 a = 1;
    #10 a = 0; b = 1;
    #10 b = 0;
    #10 c = 1;
    #10 c = 0; d = 1;
    #10 d = 0;
    #20;
    $display("a ##1 b or c ##1 d ends at%s", with_or_ends);
    $display("a or c ends at%s", either_ends);
    $finish;
  end
endmodule
