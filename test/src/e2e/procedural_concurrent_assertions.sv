module procedural_concurrent_assertions;
  logic mclk = 0, scanclk = 0, fastclk = 0, clock = 0;
  logic reset = 0;
  logic d1 = 0, d = 1, q = 0;
  logic d2 = 1, q2 = 0;
  int cnt = 0;
  int p1_pass = 0, p1_fail = 0, loop_pass = 0, loop_fail = 0;
  int p4_pass = 0, p4_fail = 0, c_hits = 0;
  always #10 mclk = ~mclk;
  always #20 scanclk = ~scanclk;
  always #5 fastclk = ~fastclk;
  always #15 clock = ~clock;

  default clocking dc @(posedge scanclk); endclocking

  property r1;
    q != d;
  endproperty
  always @(posedge mclk) begin
    q <= d1;
    r1_p1: assert property (r1) p1_pass++; else p1_fail++;
    r1_p2: assert property (@(posedge scanclk) r1)
      $display("r1_p2 passed at %0d", $time);
    else $display("r1_p2 failed at %0d", $time);
    r1_p3: assert property (@(posedge fastclk) r1)
      $display("r1_p3 passed at %0d", $time);
    else $display("r1_p3 failed at %0d", $time);
    for (int i = 0; i < 3; i++)
      loop_p: assert property (r1) loop_pass++; else loop_fail++;
    c_p: cover property (q == d1) c_hits++;
  end

  property r2;
    q2 != d2;
  endproperty
  always_ff @(posedge clock iff reset == 0 or posedge reset) begin
    cnt <= reset ? 0 : cnt + 1;
    q2 <= d2;
    r2_p: assert property (r2);
  end

  initial begin
    #12;
    r4_p: assert property (r1) p4_pass++; else p4_fail++;
  end

  initial begin
    #25 d1 = 1;
    #15 reset = 1;
    #10 reset = 0;
    #15 d1 = 0;
    #55 $display("r1_p1 passes %0d fails %0d", p1_pass, p1_fail);
    $display("loop_p passes %0d fails %0d", loop_pass, loop_fail);
    $display("r4_p passes %0d fails %0d", p4_pass, p4_fail);
    $display("c_p covered %0d times", c_hits);
    $finish;
  end
endmodule
