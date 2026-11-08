module sequence_intersect;
  logic clk = 0;
  int tick = 1;
  logic te1, te2, te3, te4, te5;
  string intersect_ends = "";
  string and_ends = "";
  string pairs_ends = "";
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign te1 = tick inside {1, 2, 8, 15, 16, 22, 29, 30, 36};
  assign te2 = tick inside {9, 10, 11, 12, 13, 24, 26, 38};
  assign te3 = tick inside {2, 3, 8, 16, 17, 22, 30, 31, 36};
  assign te4 = tick inside {4, 10, 18, 24, 32, 38};
  assign te5 = tick inside {6, 12, 20, 24, 26, 34, 40};

  sequence same_length;
    @(posedge clk) (te1 ##[1:5] te2) intersect (te3 ##2 te4 ##2 te5);
  endsequence

  sequence any_length;
    @(posedge clk) (te1 ##[1:5] te2) and (te3 ##2 te4 ##2 te5);
  endsequence

  sequence pairs;
    @(posedge clk) (te1 ##[1:5] te2) intersect (te3 ##2 te4 ##[0:2] te5);
  endsequence

  initial forever begin
    wait (same_length.triggered);
    intersect_ends = $sformatf("%s %0d", intersect_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (any_length.triggered);
    and_ends = $sformatf("%s %0d", and_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (pairs.triggered);
    pairs_ends = $sformatf("%s %0d", pairs_ends, $time);
    @(posedge clk);
  end

  initial begin
    #430;
    $display("(te1 ##[1:5] te2) intersect (te3 ##2 te4 ##2 te5) ends at%s",
             intersect_ends);
    $display("(te1 ##[1:5] te2) and (te3 ##2 te4 ##2 te5) ends at%s",
             and_ends);
    $display("(te1 ##[1:5] te2) intersect (te3 ##2 te4 ##[0:2] te5) ends at%s",
             pairs_ends);
    $finish;
  end
endmodule
