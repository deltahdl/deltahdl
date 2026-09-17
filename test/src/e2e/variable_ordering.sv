// §18.5.9 variable ordering: the solver gives a uniform distribution over the
// legal value combinations, so where a 1-bit s implies a 32-bit d is zero, s
// is true in one of the 1 + 2^32 legal combinations and is drawn true as
// good as never; solve...before orders the solve so that s is chosen first,
// 0 or 1 with equal probability, and d then subject to it; the ordering
// changes no legal combination and cannot make the solver fail; and the
// variables may be solved in an order the ordering does not give where the
// outcome is the same, the clause's x held to 0 and below y under solve y
// before x. The Unordered and the Ordered below are the clause's B, 1024
// draws each, the Chained orders a before b and b before c under a -> b == 0
// and b == 0 -> c == 0, 1024 times, and the Fixed is the clause's x and y,
// 64 times. Over the draws no draw of the Unordered has s set; the Ordered
// has s set in between 400 and 624 draws, d zero on every draw with s set
// and nonzero on some draw without, and every randomize() succeeding; the
// Chained has a set in between 400 and 624 draws, b zero on every draw with
// a set and c zero on every draw with b zero; and the Fixed holds x at 0 and
// y above it on every draw, every randomize() succeeding. Each line prints
// whether the count met what the clause determines and never a value the
// generator chose.
class Unordered;
  rand bit s;
  rand bit [31:0] d;
  constraint c { s -> d == 0; }
endclass

class Ordered;
  rand bit s;
  rand bit [31:0] d;
  constraint c { s -> d == 0; }
  constraint order { solve s before d; }
endclass

class Chained;
  rand bit a;
  rand bit [1:0] b;
  rand bit [3:0] c;
  constraint k { a -> b == 0; b == 0 -> c == 0; }
  constraint order { solve a before b; solve b before c; }
endclass

class Fixed;
  rand bit [3:0] x;
  rand bit [3:0] y;
  constraint k { x == 0; x < y; }
  constraint order { solve y before x; }
endclass

module variable_ordering;
  int unordered_set = 0, ordered_set = 0, zero_when_set = 0, free = 0;
  int ordered_ok = 0, chained_set = 0, chained_ok = 0, fixed_ok = 0;
  initial begin
    Unordered u = new;
    Ordered o = new;
    Chained h = new;
    Fixed f = new;
    repeat (1024) begin
      void'(u.randomize());
      if (u.s) unordered_set++;
    end
    repeat (1024) begin
      if (o.randomize()) ordered_ok++;
      if (o.s) begin
        ordered_set++;
        if (o.d == 0) zero_when_set++;
      end else if (o.d != 0) free = 1;
    end
    repeat (1024) begin
      void'(h.randomize());
      if (h.a) chained_set++;
      if ((!h.a || h.b == 0) && (h.b != 0 || h.c == 0)) chained_ok++;
    end
    repeat (64) begin
      if (f.randomize() && f.x == 0 && f.y > 0) fixed_ok++;
    end
    $display("s set without ordering: %0d of 1024", unordered_set);
    $display("s set with ordering near half: %0d, d zero whenever s is set: %0d",
             ordered_set > 400 && ordered_set < 624,
             zero_when_set == ordered_set);
    $display("d drawn freely without s: %0d, every ordered solve succeeds: %0d",
             free, ordered_ok);
    $display("a set near half: %0d, both implications hold: %0d of 1024",
             chained_set > 400 && chained_set < 624, chained_ok);
    $display("x at 0 below y on every solve: %0d of 64", fixed_ok);
    $finish;
  end
endmodule
