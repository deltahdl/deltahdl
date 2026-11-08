module negation_property;
  logic clk = 0;
  int tick = 1;
  logic a, b, busy;
  int a1_pass = 0, a1_fail = 0;
  int a2_pass = 0, a2_fail = 0;
  int a3_pass = 0, a3_fail = 0;
  int a4_pass = 0, a4_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign a = tick inside {1, 2, 4};
  assign b = tick inside {2};
  assign busy = tick inside {3};

  a1: assert property (@(posedge clk) not a ##1 b)
    a1_pass++; else begin
      a1_fail++;
      if ($time == 40) $display("not a ##1 b fails at the end of the run");
    end

  a2: assert property (@(posedge clk) not strong(a ##1 b))
    a2_pass++; else begin
      a2_fail++;
      if ($time == 40)
        $display("not strong(a ##1 b) fails at the end of the run");
    end

  a3: assert property (@(posedge clk) not busy) a3_pass++; else a3_fail++;

  property p_idle;
    @(posedge clk) not busy;
  endproperty

  a4: assert property (p_idle) a4_pass++; else a4_fail++;

  initial begin
    #40;
    $display("not a ##1 b passes %0d fails %0d at ticks", a1_pass, a1_fail);
    $display("not strong(a ##1 b) passes %0d fails %0d at ticks", a2_pass,
             a2_fail);
    $display("not busy passes %0d fails %0d", a3_pass, a3_fail);
    $display("p_idle passes %0d fails %0d", a4_pass, a4_fail);
    $finish;
  end
endmodule
