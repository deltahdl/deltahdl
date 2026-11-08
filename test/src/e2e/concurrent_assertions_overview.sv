module concurrent_assertions_overview;
  logic clk = 0;
  logic a = 0;
  int ticks = 0;

  always #5 clk = ~clk;

  always @(posedge clk) begin
    ticks = ticks + 1;
    $display("tick %0d at %0d", ticks, $time);
  end

  a_low: assert property (@(posedge clk) !a)
    $display("a_low: passed at %0d, a is now %0d", $time, a);
  else
    $display("a_low: failed at %0d, a is now %0d", $time, a);

  initial begin
    #7 a = 1;
    #3 a = 0;
    #15 a = 1;
    #12 a = 0;
    #13 $finish;
  end
endmodule
