// §18.5.10 static constraint blocks: a constraint block declared static has
// calls to constraint_mode() affect all instances of the constraint in all
// objects, so a static constraint set to off is off for every instance of
// the class, while a block that is not static keeps a mode of its own per
// object; and a constraint declared through a prototype and an external
// block carries the static keyword on both or on neither. The Shared below
// holds a static bounded, x below 10, beside an even that is not static; the
// Own holds the same bounded without static; and the Completed declares a
// static prototype nonzero completed by a static external block holding x
// above 0. Over 64 draws of each of two Shared every draw is below 10 and
// even; with bounded turned off through the first, the second reports it
// off, some of its 64 draws reach 10 or more and every one is still even;
// turned back on through the second, the first reports it on and its 64
// draws are all below 10 again. With bounded turned off through the first
// of two Own, the second reports it on and its 64 draws all stay below 10.
// The two Completed draw x above 0 on every one of 64 draws each, and the
// block turned off through one is off through the other. Each line prints
// whether the count met what the clause determines and never a value the
// generator chose.
class Shared;
  rand bit [7:0] x;
  static constraint bounded { x < 10; }
  constraint even { x % 2 == 0; }
endclass

class Own;
  rand bit [7:0] x;
  constraint bounded { x < 10; }
endclass

class Completed;
  rand bit [7:0] x;
  static constraint nonzero;
endclass

static constraint Completed::nonzero { x > 0; }

module static_constraint_blocks;
  int both = 0, freed = 0, still_even = 0, back = 0, own_kept = 0;
  int completed = 0;
  initial begin
    Shared s1 = new;
    Shared s2 = new;
    Own o1 = new;
    Own o2 = new;
    Completed c1 = new;
    Completed c2 = new;
    repeat (64) begin
      void'(s1.randomize());
      void'(s2.randomize());
      if (s1.x < 10 && s1.x % 2 == 0 && s2.x < 10 && s2.x % 2 == 0) both++;
    end
    s1.bounded.constraint_mode(0);
    $display("bounded off through the other instance: %0d",
             s2.bounded.constraint_mode() == 0);
    repeat (64) begin
      void'(s2.randomize());
      if (s2.x >= 10) freed = 1;
      if (s2.x % 2 == 0) still_even++;
    end
    s2.bounded.constraint_mode(1);
    $display("bounded on again through the other instance: %0d",
             s1.bounded.constraint_mode() == 1);
    repeat (64) begin
      void'(s1.randomize());
      if (s1.x < 10) back++;
    end
    o1.bounded.constraint_mode(0);
    repeat (64) begin
      void'(o2.randomize());
      if (o2.x < 10) own_kept++;
    end
    repeat (64) begin
      void'(c1.randomize());
      void'(c2.randomize());
      if (c1.x > 0 && c2.x > 0) completed++;
    end
    c1.nonzero.constraint_mode(0);
    $display("both instances below 10 and even: %0d of 64", both);
    $display("freed from the bound: %0d, still even: %0d of 64", freed,
             still_even);
    $display("bounded again: %0d of 64", back);
    $display("an instance's own block stays on: %0d, below 10: %0d of 64",
             o2.bounded.constraint_mode(), own_kept);
    $display("the completed static block holds: %0d of 64, off through the other: %0d",
             completed, c2.nonzero.constraint_mode() == 0);
    $finish;
  end
endmodule
