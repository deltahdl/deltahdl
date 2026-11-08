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
    static Shared s1 = new;
    static Shared s2 = new;
    static Own o1 = new;
    static Own o2 = new;
    static Completed c1 = new;
    static Completed c2 = new;
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
