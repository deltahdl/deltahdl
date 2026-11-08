class Uniform;
  rand bit [7:0] y;
  rand real v;
  constraint c { v > 0.0 && v < 2.0; }
endclass

module rand_modifier;
  int counts[256];
  initial begin
    static Uniform u = new;
    static int repeats = 0, lower = 0, upper = 0, most = 0, drawn = 0;
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
