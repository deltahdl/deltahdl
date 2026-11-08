module nexttime_property;
  logic clk = 0;
  int tick = 1;
  logic a;
  int weak_pass = 0, weak_fail = 0;
  int strong_pass = 0, strong_fail = 0;
  int two_pass = 0, two_fail = 0;
  int stwo_pass = 0, stwo_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign a = tick inside {2, 3};

  weak_next: assert property (@(posedge clk) nexttime a)
    begin
      weak_pass++;
      if ($time == 40) $display("nexttime a passes at the end of the run");
    end else weak_fail++;

  strong_next: assert property (@(posedge clk) s_nexttime a)
    strong_pass++; else begin
      strong_fail++;
      if ($time == 40) $display("s_nexttime a fails at the end of the run");
    end

  weak_two: assert property (@(posedge clk) nexttime [2] a)
    begin
      two_pass++;
      if ($time == 40) $display("nexttime [2] a passes at the end of the run");
    end else two_fail++;

  strong_two: assert property (@(posedge clk) s_nexttime [2] a)
    stwo_pass++; else begin
      stwo_fail++;
      if ($time == 40)
        $display("s_nexttime [2] a fails at the end of the run");
    end

  initial begin
    #40;
    $display("nexttime a passes %0d fails %0d at ticks", weak_pass, weak_fail);
    $display("s_nexttime a passes %0d fails %0d at ticks", strong_pass,
             strong_fail);
    $display("nexttime [2] a passes %0d fails %0d at ticks", two_pass,
             two_fail);
    $display("s_nexttime [2] a passes %0d fails %0d at ticks", stwo_pass,
             stwo_fail);
    $finish;
  end
endmodule
