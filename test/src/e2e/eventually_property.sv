module eventually_property;
  logic clk = 0;
  int tick = 1;
  logic a;
  int strong_pass = 0, strong_fail = 0;
  int ranged_pass = 0, ranged_fail = 0;
  int sranged_pass = 0, sranged_fail = 0;
  int unbounded_pass = 0, unbounded_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign a = tick inside {3};

  strong_ev: assert property (@(posedge clk) s_eventually a)
    strong_pass++; else begin
      strong_fail++;
      if ($time == 40) $display("s_eventually a fails at the end of the run");
    end

  ranged: assert property (@(posedge clk) eventually [0:1] a)
    begin
      ranged_pass++;
      if ($time == 40)
        $display("eventually [0:1] a passes at the end of the run");
    end else ranged_fail++;

  strong_ranged: assert property (@(posedge clk) s_eventually [0:1] a)
    sranged_pass++; else begin
      sranged_fail++;
      if ($time == 40)
        $display("s_eventually [0:1] a fails at the end of the run");
    end

  unbounded: assert property (@(posedge clk) s_eventually [2:$] a)
    unbounded_pass++; else begin
      unbounded_fail++;
      if ($time == 40)
        $display("s_eventually [2:$] a fails at the end of the run");
    end

  initial begin
    #40;
    $display("s_eventually a passes %0d fails %0d at ticks", strong_pass,
             strong_fail);
    $display("eventually [0:1] a passes %0d fails %0d at ticks", ranged_pass,
             ranged_fail);
    $display("s_eventually [0:1] a passes %0d fails %0d at ticks",
             sranged_pass, sranged_fail);
    $display("s_eventually [2:$] a passes %0d fails %0d at ticks",
             unbounded_pass, unbounded_fail);
    $finish;
  end
endmodule
