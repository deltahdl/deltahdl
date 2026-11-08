module semantic_leading_clocks;
  logic clk1 = 0;
  wire clk2;
  logic a = 1, b = 0, c = 0;
  assign clk2 = clk1;
  always #5 clk1 = ~clk1;

  a2: assert property (@(clk1) a and @(clk1) b)
    $display("a2 passed at %0d", $time); else;

  always @(posedge clk1) begin
    a4: assert property (a and @(posedge clk1) c)
      $display("a4 passed at %0d", $time); else;
  end

  c1: cover property (@(posedge clk1) a ##1 @(negedge clk1) c)
    $display("c1 covered at %0d", $time);

  initial begin
    #12 b = 1;
    #10 b = 0; c = 1;
    #10 c = 0;
    #8 $finish;
  end
endmodule
