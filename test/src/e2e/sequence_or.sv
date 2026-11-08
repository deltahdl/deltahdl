module sequence_or;
  logic clk = 0;
  int tick = 1;
  logic te1, te2, te3, te4, te5;
  string fixed_ends = "";
  string range_ends = "";
  string either_ends = "";
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign te1 = tick inside {1, 2, 8, 15, 17, 20, 22, 25, 26, 28};
  assign te2 = tick inside {9, 10, 11, 12, 13, 15, 16, 18, 19, 22, 23, 24, 28};
  assign te3 = tick inside {2, 3, 8};
  assign te4 = tick inside {10};
  assign te5 = tick inside {12};

  sequence fixed_or;
    @(posedge clk) (te1 ##2 te2) or (te3 ##2 te4 ##2 te5);
  endsequence

  sequence range_or;
    @(posedge clk) (te1 ##[1:5] te2) or (te3 ##2 te4 ##2 te5);
  endsequence

  sequence either;
    @(posedge clk) te1 or te2;
  endsequence

  initial forever begin
    wait (fixed_or.triggered);
    fixed_ends = $sformatf("%s %0d", fixed_ends, tick);
    @(posedge clk);
  end
  initial forever begin
    wait (range_or.triggered);
    range_ends = $sformatf("%s %0d", range_ends, tick);
    @(posedge clk);
  end
  initial forever begin
    wait (either.triggered);
    either_ends = $sformatf("%s %0d", either_ends, tick);
    @(posedge clk);
  end

  initial begin
    #290;
    $display("(te1 ##2 te2) or (te3 ##2 te4 ##2 te5) ends at ticks%s",
             fixed_ends);
    $display("(te1 ##[1:5] te2) or (te3 ##2 te4 ##2 te5) ends at ticks%s",
             range_ends);
    $display("te1 or te2 ends at ticks%s", either_ends);
    $finish;
  end
endmodule
