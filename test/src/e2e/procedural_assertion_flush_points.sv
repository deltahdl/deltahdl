module procedural_assertion_flush_points;
  logic clk = 0;
  logic a = 0, not_a;
  logic a2_a = 0, a2_b = 0;
  logic src = 0, ca, cb;
  int a1_pass = 0, a1_fail = 0;
  always #5 clk = ~clk;
  assign not_a = !a;
  assign ca = src;
  assign cb = src;

  default clocking @(posedge clk); endclocking

  always_comb begin : b1
    a1: assert property (const'(not_a) != const'(a)) a1_pass++;
    else a1_fail++;
  end

  always @(a2_a or a2_b) begin : b2
    a2: assert property (const'(a2_a) == const'(a2_b))
      $display("a2 passed at %0d", $time);
    else $display("a2 failed at %0d", $time);
    #1;
    a3: assert property (const'(a2_a) == const'(a2_b))
      $display("a3 passed at %0d", $time);
    else $display("a3 failed at %0d", $time);
    a2_b <= a2_a;
  end

  always_comb begin : b3
    c1: cover property (const'(cb) != const'(ca));
  end

  initial begin
    #10 a2_a = 1;
    #5 a = 1;
    #5 a = 0;
    #5 src = 1;
    #10 src = 0;
    #15 $display("a1 passes %0d fails %0d", a1_pass, a1_fail);
    $finish;
  end
endmodule
