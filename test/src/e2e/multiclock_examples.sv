module multiclock_examples;
  logic clk = 0;
  logic clk1 = 0;
  logic clk2 = 0;
  int tick = 1;
  logic a, b, c, d, e, f;
  int s_pass = 0, s_fail = 0;
  int p1_pass = 0, p1_fail = 0;
  int p2_pass = 0, p2_fail = 0;
  int p3_pass = 0, p3_fail = 0;
  int p6_pass = 0, p6_fail = 0;
  int p7_pass = 0, p7_fail = 0;
  int p8_pass = 0, p8_fail = 0;
  string s_at = "", p1_at = "", p2_at = "", p3_at = "", p6_at = "", p7_at = "",
         p8_at = "";
  always #5 clk = ~clk;
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

  assign a = tick inside {1, 2};
  assign b = tick inside {3, 5};
  assign c = tick inside {3, 4, 6};
  assign d = tick inside {6, 7};
  assign e = tick inside {3};
  assign f = tick inside {4};

  sequence s1;
    a ##1 b;
  endsequence
  sequence s2;
    c ##1 d;
  endsequence

  sequence mult_s;
    @(posedge clk) a ##1 @(posedge clk1) s1 ##1 @(posedge clk2) s2;
  endsequence

  property mult_p1;
    @(posedge clk) a ##1 @(posedge clk1) s1 ##1 @(posedge clk2) s2;
  endproperty

  property mult_p2;
    mult_s;
  endproperty

  property mult_p3;
    @(posedge clk) a ##1 @(posedge clk1) s1 |=> @(posedge clk2) s2;
  endproperty

  property mult_p6;
    mult_s |=> mult_s;
  endproperty

  property mult_p7;
    @(posedge clk) a ##1 b |-> c ##1 @(posedge clk1) d;
  endproperty

  property mult_p8;
    @(posedge clk) a ##1 b |->
      if (c)
        (1 |=> @(posedge clk1) d)
      else
        e ##1 @(posedge clk2) f ;
  endproperty

  as_s: assert property (mult_s)
    s_pass++;
    else begin
      s_fail++;
      s_at = $sformatf("%s %0d", s_at, $time);
    end

  as_p1: assert property (mult_p1)
    p1_pass++;
    else begin
      p1_fail++;
      p1_at = $sformatf("%s %0d", p1_at, $time);
    end

  as_p2: assert property (mult_p2)
    p2_pass++;
    else begin
      p2_fail++;
      p2_at = $sformatf("%s %0d", p2_at, $time);
    end

  as_p3: assert property (mult_p3)
    p3_pass++;
    else begin
      p3_fail++;
      p3_at = $sformatf("%s %0d", p3_at, $time);
    end

  as_p6: assert property (mult_p6)
    p6_pass++;
    else begin
      p6_fail++;
      p6_at = $sformatf("%s %0d", p6_at, $time);
    end

  as_p7: assert property (mult_p7)
    p7_pass++;
    else begin
      p7_fail++;
      p7_at = $sformatf("%s %0d", p7_at, $time);
    end

  as_p8: assert property (mult_p8)
    p8_pass++;
    else begin
      p8_fail++;
      p8_at = $sformatf("%s %0d", p8_at, $time);
    end

  initial begin
    #80;
    $display("mult_s passes %0d fails %0d at%s", s_pass, s_fail, s_at);
    $display("mult_p1 passes %0d fails %0d at%s", p1_pass, p1_fail, p1_at);
    $display("mult_p2 passes %0d fails %0d at%s", p2_pass, p2_fail, p2_at);
    $display("mult_p3 passes %0d fails %0d at%s", p3_pass, p3_fail, p3_at);
    $display("mult_p6 passes %0d fails %0d at%s", p6_pass, p6_fail, p6_at);
    $display("mult_p7 passes %0d fails %0d at%s", p7_pass, p7_fail, p7_at);
    $display("mult_p8 passes %0d fails %0d at%s", p8_pass, p8_fail, p8_at);
    $finish;
  end
endmodule
