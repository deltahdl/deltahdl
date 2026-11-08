module weak_strong_operators;
  logic clk = 0;
  int tick = 1;
  logic a = 1, b = 0, c;
  int next_pass = 0, next_fail = 0;
  int snext_pass = 0, snext_fail = 0;
  int always_pass = 0, always_fail = 0;
  int salways_pass = 0, salways_fail = 0;
  int ev_pass = 0, ev_fail = 0;
  int sev_pass = 0, sev_fail = 0;
  int until_pass = 0, until_fail = 0;
  int suntil_pass = 0, suntil_fail = 0;
  int weak_pass = 0, weak_fail = 0;
  int strong_pass = 0, strong_fail = 0;
  int safety_pass = 0, safety_fail = 0;
  initial repeat (6) #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign c = tick inside {1, 2};

  next: assert property (@(posedge clk) nexttime a)
    begin
      next_pass++;
      if ($time == 100) $display("nexttime a passes at the end of the run");
    end else next_fail++;

  strong_next: assert property (@(posedge clk) s_nexttime a)
    snext_pass++; else begin
      snext_fail++;
      if ($time == 100) $display("s_nexttime a fails at the end of the run");
    end

  weak_always: assert property (@(posedge clk) always a)
    begin
      always_pass++;
      if ($time == 100) $display("always a passes at the end of the run");
    end else always_fail++;

  strong_always: assert property (@(posedge clk) s_always [0:3] a)
    salways_pass++; else begin
      salways_fail++;
      if ($time == 100)
        $display("s_always [0:3] a fails at the end of the run");
    end

  weak_ev: assert property (@(posedge clk) eventually [0:3] b)
    begin
      ev_pass++;
      if ($time == 100)
        $display("eventually [0:3] b passes at the end of the run");
    end else ev_fail++;

  strong_ev: assert property (@(posedge clk) s_eventually b)
    sev_pass++; else begin
      sev_fail++;
      if ($time == 100) $display("s_eventually b fails at the end of the run");
    end

  weak_until: assert property (@(posedge clk) a until b)
    begin
      until_pass++;
      if ($time == 100) $display("a until b passes at the end of the run");
    end else until_fail++;

  strong_until: assert property (@(posedge clk) a s_until b)
    suntil_pass++; else begin
      suntil_fail++;
      if ($time == 100) $display("a s_until b fails at the end of the run");
    end

  weak_seq: assert property (@(posedge clk) weak(a ##1 a))
    weak_pass++; else weak_fail++;

  strong_seq: assert property (@(posedge clk) strong(a ##1 a))
    strong_pass++; else begin
      strong_fail++;
      if ($time == 100)
        $display("strong(a ##1 a) fails at the end of the run");
    end

  safety: assert property (@(posedge clk) always c)
    safety_pass++; else begin
      safety_fail++;
      if (safety_fail == 1)
        $display("always c fails at time %0d with the clock still ticking",
                 $time);
    end

  initial begin
    #100;
    $display("nexttime a passes %0d fails %0d at ticks", next_pass,
             next_fail);
    $display("s_nexttime a passes %0d fails %0d at ticks", snext_pass,
             snext_fail);
    $display("always a passes %0d fails %0d at ticks", always_pass,
             always_fail);
    $display("s_always [0:3] a passes %0d fails %0d at ticks", salways_pass,
             salways_fail);
    $display("eventually [0:3] b passes %0d fails %0d at ticks", ev_pass,
             ev_fail);
    $display("s_eventually b passes %0d fails %0d at ticks", sev_pass,
             sev_fail);
    $display("a until b passes %0d fails %0d at ticks", until_pass,
             until_fail);
    $display("a s_until b passes %0d fails %0d at ticks", suntil_pass,
             suntil_fail);
    $display("weak(a ##1 a) passes %0d fails %0d at ticks", weak_pass,
             weak_fail);
    $display("strong(a ##1 a) passes %0d fails %0d at ticks", strong_pass,
             strong_fail);
    $display("always c passes %0d fails %0d at ticks", safety_pass,
             safety_fail);
    $finish;
  end
endmodule
