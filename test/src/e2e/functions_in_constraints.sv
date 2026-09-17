// §18.5.11 functions in constraints: a constraint expression can call a
// function, which is called before the constraints are solved with its
// return value treated as a state variable, and a random variable used as a
// function argument establishes an implicit variable ordering, the
// constraints over the higher-priority variables solved first and those
// variables state variables to the rest, with the cyclic variables solved
// first within each prioritized set. The Counted below is the clause's
// count_ones, a function looping over the bits of a 10-bit v to which C1
// holds length; the Prioritized is the clause's B, x held at most F(y) under
// y inside {2, 4, 8}, with x of 5 bits and F tripling its argument; and the
// Cycled holds x to G(r) over a randc r of 2 bits, G adding one. Over 128
// draws of the Counted length equals the ones the module counts in v; over
// 1200 draws of the Prioritized x is at most three times y on every draw and
// y takes each of 2, 4 and 8 in near a third of the draws, y solved first
// from its own set, where a joint draw over the legal combinations would
// give y the 8 that admits the most x far more often; and over 4 draws of
// the Cycled r takes each of its four values once and x follows it as G
// gives. Each line prints whether the count met what the clause determines
// and never a value the generator chose.
class Counted;
  rand bit [9:0] v;
  rand int length;
  constraint C1 { length == count_ones(v); }
  function int count_ones(bit [9:0] w);
    int n;
    for (n = 0; w != 0; w = w >> 1)
      n += w & 1'b1;
    return n;
  endfunction
endclass

class Prioritized;
  rand bit [4:0] x;
  rand int y;
  constraint C { x <= F(y); }
  constraint D { y inside {2, 4, 8}; }
  function int F(int a);
    return 3 * a;
  endfunction
endclass

class Cycled;
  randc bit [1:0] r;
  rand bit [3:0] x;
  constraint C { x == G(r); }
  function int G(bit [1:0] a);
    return a + 1;
  endfunction
endclass

module functions_in_constraints;
  int counted = 0, ones = 0, bounded = 0, twos = 0, fours = 0, eights = 0;
  int seen = 0, followed = 0;
  initial begin
    Counted c = new;
    Prioritized p = new;
    Cycled y = new;
    repeat (128) begin
      void'(c.randomize());
      ones = 0;
      for (int i = 0; i < 10; i++) if (c.v[i]) ones++;
      if (c.length == ones) counted++;
    end
    repeat (1200) begin
      void'(p.randomize());
      if (p.x <= 3 * p.y) bounded++;
      if (p.y == 2) twos++;
      if (p.y == 4) fours++;
      if (p.y == 8) eights++;
    end
    repeat (4) begin
      void'(y.randomize());
      seen = seen | (1 << y.r);
      if (y.x == y.r + 1) followed++;
    end
    $display("length equals the ones counted in v: %0d of 128", counted);
    $display("x at most F(y): %0d of 1200, y near a third each: %0d", bounded,
             twos > 300 && twos < 500 && fours > 300 && fours < 500 &&
             eights > 300 && eights < 500);
    $display("a cyclic argument takes every value: %0d, x follows it: %0d of 4",
             seen == 15, followed);
    $finish;
  end
endmodule
