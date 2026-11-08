module first_match_operation;
  logic clk = 0;
  int tick = 1;
  logic te1, te2, a, b, c, d;
  string t1_ends = "";
  string ts1_ends = "";
  string t2_ends = "";
  string ts2_ends = "";
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign te1 = tick inside {1};
  assign te2 = tick inside {3, 4, 5, 6};
  assign a = tick inside {11, 21};
  assign b = tick inside {13, 14, 23};
  assign c = tick inside {11, 21};
  assign d = tick inside {13, 22};

  sequence t1;
    @(posedge clk) te1 ##[2:5] te2;
  endsequence

  sequence ts1;
    @(posedge clk) first_match(te1 ##[2:5] te2);
  endsequence

  sequence t2;
    @(posedge clk) (a ##[2:3] b) or (c ##[1:2] d);
  endsequence

  sequence ts2;
    @(posedge clk) first_match(t2);
  endsequence

  initial forever begin
    wait (t1.triggered);
    t1_ends = $sformatf("%s %0d", t1_ends, tick);
    @(posedge clk);
  end
  initial forever begin
    wait (ts1.triggered);
    ts1_ends = $sformatf("%s %0d", ts1_ends, tick);
    @(posedge clk);
  end
  initial forever begin
    wait (t2.triggered);
    t2_ends = $sformatf("%s %0d", t2_ends, tick);
    @(posedge clk);
  end
  initial forever begin
    wait (ts2.triggered);
    ts2_ends = $sformatf("%s %0d", ts2_ends, tick);
    @(posedge clk);
  end

  initial begin
    #250;
    $display("te1 ##[2:5] te2 ends at ticks%s", t1_ends);
    $display("first_match(te1 ##[2:5] te2) ends at ticks%s", ts1_ends);
    $display("(a ##[2:3] b) or (c ##[1:2] d) ends at ticks%s", t2_ends);
    $display("first_match(t2) ends at ticks%s", ts2_ends);
    $finish;
  end
endmodule
