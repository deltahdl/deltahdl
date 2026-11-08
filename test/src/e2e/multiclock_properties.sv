module multiclock_properties;
  logic clk0 = 0;
  logic clk1 = 0;
  logic clk2 = 0;
  int tick = 1;
  logic sig0, sig1, b, s1, s2;
  int conj_pass = 0, conj_fail = 0;
  int nonover_pass = 0, nonover_fail = 0;
  int over_pass = 0, over_fail = 0;
  int ifelse_pass = 0, ifelse_fail = 0;
  string conj_at = "", nonover_at = "", over_at = "", ifelse_at = "";
  always #5 clk0 = ~clk0;
  always #10 tick = tick + 1;
  initial begin
    #12 clk1 = 1;
    #8 clk1 = 0;
    #7 clk1 = 1;
    #8 clk1 = 0;
    #10 clk1 = 1;
    #5 clk1 = 0;
    #7 clk1 = 1;
    #8 clk1 = 0;
    #7 clk1 = 1;
    #6 clk1 = 0;
  end
  initial begin
    #8 clk2 = 1;
    #8 clk2 = 0;
    #9 clk2 = 1;
    #7 clk2 = 0;
    #6 clk2 = 1;
    #8 clk2 = 0;
    #9 clk2 = 1;
    #7 clk2 = 0;
    #8 clk2 = 1;
    #4 clk2 = 0;
    #4 clk2 = 1;
    #1 clk2 = 0;
  end

  assign sig0 = tick inside {1, 2, 5, 7};
  assign sig1 = tick inside {3, 5};
  assign b = tick inside {1, 3, 6};
  assign s1 = tick inside {2, 3};
  assign s2 = tick inside {4, 7};

  conj: assert property (@(posedge clk0)
                         1 |-> (@(posedge clk0) sig0) and (@(posedge clk1) sig1))
    begin
      conj_pass++;
      conj_at = $sformatf("%s %0d", conj_at, $time);
    end else conj_fail++;

  nonover: assert property (@(posedge clk0) sig0 |=> @(posedge clk1) sig1)
    begin
      nonover_pass++;
      nonover_at = $sformatf("%s %0d", nonover_at, $time);
    end else nonover_fail++;

  over: assert property (@(posedge clk0) sig0 |-> @(posedge clk1) sig1)
    begin
      over_pass++;
      over_at = $sformatf("%s %0d", over_at, $time);
    end else over_fail++;

  ifelse: assert property (@(posedge clk0)
                           if (b) @(posedge clk1) s1 else @(posedge clk2) s2)
    begin
      ifelse_pass++;
      ifelse_at = $sformatf("%s %0d", ifelse_at, $time);
    end else ifelse_fail++;

  initial begin
    #80;
    $display("1 |-> (@(posedge clk0) sig0) and (@(posedge clk1) sig1) passes %0d fails %0d at%s",
             conj_pass, conj_fail, conj_at);
    $display("sig0 |=> @(posedge clk1) sig1 passes %0d fails %0d at%s",
             nonover_pass, nonover_fail, nonover_at);
    $display("sig0 |-> @(posedge clk1) sig1 passes %0d fails %0d at%s",
             over_pass, over_fail, over_at);
    $display("if (b) @(posedge clk1) s1 else @(posedge clk2) s2 passes %0d fails %0d at%s",
             ifelse_pass, ifelse_fail, ifelse_at);
    $finish;
  end
endmodule
