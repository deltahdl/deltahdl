module always_property;
  logic clk = 0;
  int tick = 1;
  logic a, b;
  int weak_a_pass = 0, weak_a_fail = 0;
  int weak_b_pass = 0, weak_b_fail = 0;
  int ranged_pass = 0, ranged_fail = 0;
  int strong_pass = 0, strong_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign a = tick inside {1, 2, 3};
  assign b = tick inside {1, 2, 3, 4};

  weak_a: assert property (@(posedge clk) always a)
    weak_a_pass++; else weak_a_fail++;

  weak_b: assert property (@(posedge clk) always b)
    begin
      weak_b_pass++;
      if ($time == 40) $display("always b passes at the end of the run");
    end else weak_b_fail++;

  ranged: assert property (@(posedge clk) always [0:1] b)
    begin
      ranged_pass++;
      if ($time == 40) $display("always [0:1] b passes at the end of the run");
    end else ranged_fail++;

  strong_ranged: assert property (@(posedge clk) s_always [0:1] b)
    strong_pass++; else begin
      strong_fail++;
      if ($time == 40) $display("s_always [0:1] b fails at the end of the run");
    end

  initial begin
    #40;
    $display("always a passes %0d fails %0d", weak_a_pass, weak_a_fail);
    $display("always b passes %0d fails %0d at ticks", weak_b_pass,
             weak_b_fail);
    $display("always [0:1] b passes %0d fails %0d at ticks", ranged_pass,
             ranged_fail);
    $display("s_always [0:1] b passes %0d fails %0d at ticks", strong_pass,
             strong_fail);
    $finish;
  end
endmodule
