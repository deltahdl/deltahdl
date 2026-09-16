// §18.4.1 Rand modifier: a variable declared rand is a standard random
// variable whose values are uniformly distributed over its range, so an
// unconstrained rand bit [7:0] is assigned any value from 0 to 255 with
// equal probability, the chance of the same value on successive calls
// being 1/256, and a rand real is uniformly distributed over its range,
// the real v constrained to 0.0 to 2.0 landing in 0.0 to 1.0 as often as in
// 1.0 to 2.0. Over 8192 randomizations every one of the 256 values of y is
// drawn, none more than twice its share of 32, successive calls repeat a
// value about 1/256 of the time, within 64 repeats where 32 are expected,
// and the two halves of v's range receive counts within a tenth of each
// other; each line prints whether the count met what a uniform draw
// determines and never a value the generator chose.
class Uniform;
  rand bit [7:0] y;
  rand real v;
  constraint c { v > 0.0 && v < 2.0; }
endclass

module rand_modifier;
  int counts[256];
  initial begin
    Uniform u = new;
    int repeats = 0, lower = 0, upper = 0, most = 0, drawn = 0;
    bit [7:0] last;
    for (int i = 0; i < 8192; i++) begin
      void'(u.randomize());
      counts[u.y]++;
      if (i > 0 && u.y == last) repeats++;
      last = u.y;
      if (u.v < 1.0) lower++; else upper++;
    end
    for (int k = 0; k < 256; k++) begin
      if (counts[k] > 0) drawn++;
      if (counts[k] > most) most = counts[k];
    end
    $display("every value of y drawn: %0d", drawn == 256);
    $display("no value of y drawn more than twice its share: %0d", most <= 64);
    $display("successive calls repeat y about 1 in 256: %0d", repeats <= 64);
    $display("halves of v's range within a tenth: %0d", (lower > upper ? lower - upper : upper - lower) <= 819);
    $finish;
  end
endmodule
