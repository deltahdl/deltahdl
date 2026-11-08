module property_examples;
  logic clk = 0;
  logic clkev = 0;
  int tick = 1;
  logic a, b, c, d, e, f;
  int r1_pass = 0, r1_fail = 0;
  int r2_pass = 0, r2_fail = 0;
  int r3_pass = 0, r3_fail = 0;
  int r4_pass = 0, r4_fail = 0;
  int r5_pass = 0, r5_fail = 0;
  int r5a_pass = 0, r5a_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;
  always @(posedge clk) clkev <= ~clkev;

  assign a = tick inside {1, 2, 3, 6};
  assign b = tick inside {1, 4, 6};
  assign c = tick inside {2, 3, 7};
  assign d = tick inside {2, 3, 5, 7};
  assign e = tick inside {5, 8};
  assign f = tick inside {3};

  property rule1;
    @(posedge clk) a |-> b ##1 c ##1 d;
  endproperty

  property rule2;
    @(clkev) disable iff (e) a |-> not (b ##1 c ##1 d);
  endproperty

  property rule3;
    @(posedge clk) a[*2] |-> ((##[1:3] c) or (d |=> e));
  endproperty

  property rule4;
    @(posedge clk) a[*2] |-> ((##[1:3] c) and (d |=> e));
  endproperty

  property rule5;
    @(posedge clk)
    a ##1 (b || c)[->1] |->
      if (b)
        (##1 d |-> e)
      else
        f;
  endproperty

  property rule6(x, y);
    ##1 x |-> y;
  endproperty

  property rule5a;
    @(posedge clk)
    a ##1 (b || c)[->1] |->
      if (b)
        rule6(d, e)
      else
        f;
  endproperty

  r1: assert property (rule1) r1_pass++; else r1_fail++;
  r2: assert property (rule2) r2_pass++; else r2_fail++;
  r3: assert property (rule3) r3_pass++; else r3_fail++;
  r4: assert property (rule4) r4_pass++; else r4_fail++;
  r5: assert property (rule5) r5_pass++; else r5_fail++;
  r5a: assert property (rule5a) r5a_pass++; else r5a_fail++;

  initial begin
    #80;
    $display("rule1 passes %0d fails %0d at ticks", r1_pass, r1_fail);
    $display("rule2 passes %0d fails %0d at ticks", r2_pass, r2_fail);
    $display("rule3 passes %0d fails %0d at ticks", r3_pass, r3_fail);
    $display("rule4 passes %0d fails %0d at ticks", r4_pass, r4_fail);
    $display("rule5 passes %0d fails %0d at ticks", r5_pass, r5_fail);
    $display("rule5a passes %0d fails %0d at ticks", r5a_pass, r5a_fail);
    $finish;
  end
endmodule
