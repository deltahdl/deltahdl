// §16.9.4 Global clocking past and future sampled value functions: the past
// functions read the value sampled at the global clock tick before, the
// future ones the value sampled at the tick after, $rising_gclk, $falling_gclk,
// $changing_gclk and $steady_gclk comparing the two, and the action block of
// an assertion holding a future function runs at the global clocking tick
// that follows the attempt's own, the default $error included. Figure 16-4 is
// driven here from its tick at 10: the global clock ticks at 10, 20, ...,
// sig is high from 0, low from 10, high from 50 and low from 80, and clk is
// high from 0, low from 10, high from 30, low from 50, high from 70, low from
// 90 and high from 110, each written in the time step of a tick, so the tick
// samples the value from before it. Table 16-2 has the future functions of
// sig read 1 at these ticks: $future_gclk at 50, 60 and 70, $rising_gclk at
// 50, $falling_gclk at 10 and 80, $changing_gclk at 10, 50 and 80, and
// $steady_gclk at the seven others through 100; the covers below count them.
// The clause's a1 holds at 10 and 50, where clk falls with sig, and is
// violated at 80, sig falling with clk steady, its $error executed at the
// tick at 90.
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

  // The past functions read the tick before, so they are usable in
  // procedural code: sig fell between the ticks at 10 and 20 as sampled, and
  // between 80 and 90, and rose between 50 and 60.
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
