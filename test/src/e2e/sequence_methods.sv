module sequence_methods;
  logic clk = 0;
  logic sysclk = 0;
  logic a = 0, b = 0, c = 0;
  logic reset = 0, inst = 0, branch_back = 0;
  logic reset1 = 0, branch_back1 = 0;
  string e3_ends = "", e4_ends = "";
  always #5 clk = ~clk;
  always #8 sysclk = ~sysclk;

  sequence e1;
    @(posedge sysclk) $rose(a) ##1 b ##1 c;
  endsequence

  sequence e2;
    @(posedge sysclk) reset ##1 inst ##1 e1.triggered ##1 branch_back;
  endsequence

  sequence e3;
    @(posedge clk) reset1 ##1 e1.matched ##1 branch_back1;
  endsequence

  sequence e2_with_arg(sequence subseq);
    @(posedge sysclk) reset ##1 inst ##1 subseq.triggered ##1 branch_back;
  endsequence

  sequence e4;
    e2_with_arg(@(posedge sysclk) $rose(a) ##1 b ##1 c);
  endsequence

  initial forever begin
    wait (e3.triggered);
    e3_ends = $sformatf("%s %0d", e3_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (e4.triggered);
    e4_ends = $sformatf("%s %0d", e4_ends, $time);
    @(posedge sysclk);
  end

  initial begin
    #10 a = 1;
    #10 reset = 1;
    #10 reset = 0; b = 1;
    #5 inst = 1;
    #10 inst = 0;
    #5 b = 0; c = 1; reset1 = 1;
    #10 reset1 = 0;
    #5 c = 0; branch_back = 1;
    #5 branch_back1 = 1;
    #5 branch_back = 0;
    #5 branch_back1 = 0;
  end

  program check;
    initial begin
      wait (e1.triggered || e2.triggered);
      if (e1.triggered) $display("e1 passed at %0d", $time);
      L2: wait (e2.triggered);
      if (e2.triggered) $display("e2 passed at %0d", $time);
      #18;
      $display("e3 with e1.matched ends at%s", e3_ends);
      $display("e4 with subseq.triggered ends at%s", e4_ends);
      $finish;
    end
  endprogram
endmodule
