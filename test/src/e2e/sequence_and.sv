module sequence_and;
  logic clk = 0;
  int tick = 1;
  logic te1, te2, te3, te4, te5;
  string fixed_ends = "";
  string range_ends = "";
  string boolean_ends = "";
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign te1 = tick inside {1, 2, 8, 15, 16, 22, 29, 31, 36, 42};
  assign te2 = tick inside {10, 12, 23, 24, 25, 26, 27, 29, 31, 33, 36, 37, 42};
  assign te3 = tick inside {2, 3, 8, 16, 17, 22};
  assign te4 = tick inside {4, 10, 18, 24};
  assign te5 = tick inside {6, 12, 20, 26};

  sequence fixed_and;
    @(posedge clk) (te1 ##2 te2) and (te3 ##2 te4 ##2 te5);
  endsequence

  sequence range_and;
    @(posedge clk) (te1 ##[1:5] te2) and (te3 ##2 te4 ##2 te5);
  endsequence

  sequence boolean_and;
    @(posedge clk) te1 and te2;
  endsequence

  initial forever begin
    wait (fixed_and.triggered);
    fixed_ends = $sformatf("%s %0d", fixed_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (range_and.triggered);
    range_ends = $sformatf("%s %0d", range_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (boolean_and.triggered);
    boolean_ends = $sformatf("%s %0d", boolean_ends, $time);
    @(posedge clk);
  end

  initial begin
    #430;
    $display("(te1 ##2 te2) and (te3 ##2 te4 ##2 te5) ends at%s", fixed_ends);
    $display("(te1 ##[1:5] te2) and (te3 ##2 te4 ##2 te5) ends at%s",
             range_ends);
    $display("te1 and te2 ends at%s", boolean_ends);
    $finish;
  end
endmodule
