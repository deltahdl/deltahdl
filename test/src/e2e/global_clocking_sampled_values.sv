module global_clocking_sampled_values;
  logic gclk = 0;
  logic clk = 1;
  logic sig = 1;
  int future_hits = 0;
  int rising_hits = 0;
  int falling_hits = 0;
  int changing_hits = 0;
  int steady_hits = 0;
  global clocking gc @(posedge gclk); endclocking

  initial begin
    #10 gclk = 1;
    forever #5 gclk = ~gclk;
  end
  initial begin
    #10 clk = 0; sig = 0;
    #20 clk = 1;
    #20 clk = 0; sig = 1;
    #20 clk = 1;
    #10 sig = 0;
    #10 clk = 0;
    #20 clk = 1;
  end

  a1: assert property (@$global_clock !$changing_gclk(sig) || $falling_gclk(clk))
  else
    $error("sig is not stable");

  cover property (@$global_clock $future_gclk(sig)) future_hits = future_hits + 1;
  cover property (@$global_clock $rising_gclk(sig)) rising_hits = rising_hits + 1;
  cover property (@$global_clock $falling_gclk(sig)) falling_hits = falling_hits + 1;
  cover property (@$global_clock $changing_gclk(sig)) changing_hits = changing_hits + 1;
  cover property (@$global_clock $steady_gclk(sig)) steady_hits = steady_hits + 1;

  always @(posedge gclk) begin
    if ($rose_gclk(sig)) $display("$rose_gclk(sig) at %0d", $time);
    if ($fell_gclk(sig)) $display("$fell_gclk(sig) at %0d", $time);
  end

  initial begin
    #115;
    $display("$future_gclk(sig) held at %0d ticks, $rising_gclk(sig) at %0d, $falling_gclk(sig) at %0d, $changing_gclk(sig) at %0d, $steady_gclk(sig) at %0d",
             future_hits, rising_hits, falling_hits, changing_hits, steady_hits);
    $finish;
  end
endmodule
