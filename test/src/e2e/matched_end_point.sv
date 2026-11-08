module matched_end_point;
  logic clk = 0;
  logic sysclk = 0;
  logic ready = 0, proc1 = 0, proc2 = 0;
  logic reset = 0, inst = 0, branch_back = 0;
  string e2_ends = "", twice_ends = "";
  always #5 clk = ~clk;
  always #8 sysclk = ~sysclk;

  sequence e1(a, b, c);
    @(posedge clk) $rose(a) ##1 b ##1 c;
  endsequence

  sequence e2;
    @(posedge sysclk) reset ##1 inst ##1 e1(ready, proc1, proc2).matched [->1]
      ##1 branch_back;
  endsequence

  sequence e1_inst;
    e1(ready, proc1, proc2);
  endsequence

  sequence twice;
    @(posedge sysclk) e1_inst.matched ##1 e1_inst.matched;
  endsequence

  initial forever begin
    wait (e2.triggered);
    e2_ends = $sformatf("%s %0d", e2_ends, $time);
    @(posedge sysclk);
  end
  initial forever begin
    wait (twice.triggered);
    twice_ends = $sformatf("%s %0d", twice_ends, $time);
    @(posedge sysclk);
  end

  initial begin
    #5 reset = 1;
    #5 reset = 0; ready = 1;
    #10 inst = 1; proc1 = 1;
    #10 inst = 0; proc1 = 0; proc2 = 1;
    #10 proc2 = 0;
    #10 ready = 0; branch_back = 1;
    #10 branch_back = 0;
    #10 reset = 1; ready = 1;
    #5 reset = 0;
    #5 inst = 1; proc1 = 1;
    #10 inst = 0; proc1 = 0; proc2 = 1;
    #10 proc2 = 0;
    #15 branch_back = 1;
    #10 branch_back = 0;
    #5;
    $display("e2 with e1(ready, proc1, proc2).matched [->1] ends at%s",
             e2_ends);
    $display("e1_inst.matched ##1 e1_inst.matched ends at%s", twice_ends);
    $finish;
  end
endmodule
