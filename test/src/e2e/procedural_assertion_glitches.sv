module procedural_assertion_glitches;
  logic clk = 0;
  logic en = 1, foo = 0, bar = 0;
  always #5 clk = ~clk;
  always @(posedge clk) bar <= ~bar;

  always_comb begin : procedural_block_1
    if (en) foo = bar;
  end

  always_comb begin : procedural_block_2
    p1: assert property (@(posedge clk) (const'(foo) == const'(bar)))
      $display("p1 passed at %0d", $time);
    else $display("p1 failed at %0d", $time);
  end

  program reactive_driver;
    initial forever @(posedge clk) if (!en) foo = bar;
  endprogram

  initial begin
    #20 en = 0;
    #20 $finish;
  end
endmodule
