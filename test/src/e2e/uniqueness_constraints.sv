// §18.5.4 Uniqueness constraints: a group of variables constrained with
// unique holds no two members at the same value after randomization. The
// group is a restricted range_list whose items are singular variables of
// integral or real type, or unpacked arrays and slices of them, all of
// equivalent type and none randc; a group of fewer than two members has
// no effect and raises no contradiction. The Trio here draws three ints
// over a three-value domain, so every draw spends the domain and no pair
// coincides; the Excluding is the clause's example on singular variables,
// b and c drawn from 4 to 6 beside an excluded held to 5 by another
// constraint, so neither takes 5 and the two split 4 and 6 between them;
// the Lone names a single member beside a relation fixing it, which the
// group leaves alone; the Reals draw two reals from the same two values
// and never alike; and the Cyclic names a randc, which is an illegal
// group that refuses randomize().
class Trio;
  rand int a;
  rand int b;
  rand int c;
  constraint dom { a inside {[0:2]}; b inside {[0:2]}; c inside {[0:2]}; }
  constraint u { unique {a, b, c}; }
endclass

class Excluding;
  rand byte b;
  rand byte c;
  rand byte excluded;
  constraint dom { b inside {[4:6]}; c inside {[4:6]}; }
  constraint u { unique {b, c, excluded}; }
  constraint exclusion { excluded == 5; }
endclass

class Lone;
  rand bit [3:0] x;
  constraint one { x == 7; unique {x}; }
endclass

class Reals;
  rand real r1;
  rand real r2;
  constraint pick {
    r1 dist { 1.0 := 1, 2.0 := 1 };
    r2 dist { 1.0 := 1, 2.0 := 1 };
  }
  constraint u { unique {r1, r2}; }
endclass

class Cyclic;
  rand bit [1:0] p;
  randc bit [1:0] q;
  constraint u { unique {p, q}; }
endclass

module uniqueness_constraints;
  int distinct = 0, split = 0, fixed = 0, apart = 0, refused = 0;
  initial begin
    Trio tr = new;
    Excluding ex = new;
    Lone lo = new;
    Reals rl = new;
    Cyclic cy = new;
    repeat (64) begin
      void'(tr.randomize());
      if (tr.a != tr.b && tr.b != tr.c && tr.a != tr.c &&
          tr.a + tr.b + tr.c == 3) distinct++;
    end
    $display("no two of three members over a three-value domain coincide: %0d of 64",
             distinct);
    repeat (64) begin
      void'(ex.randomize());
      if (ex.excluded == 5 && ex.b != 5 && ex.c != 5 && ex.b + ex.c == 10)
        split++;
    end
    $display("the members beside excluded avoid its 5 and split 4 and 6: %0d of 64",
             split);
    repeat (32) begin
      if (lo.randomize() && lo.x == 7) fixed++;
    end
    $display("a group of one member has no effect and no contradiction: %0d of 32",
             fixed);
    repeat (64) begin
      void'(rl.randomize());
      if (rl.r1 != rl.r2 && rl.r1 + rl.r2 == 3.0) apart++;
    end
    $display("two real members never draw alike: %0d of 64", apart);
    if (cy.randomize() == 0) refused = 1;
    $display("a group holding a randc refuses randomize(): %0d", refused);
    $finish;
  end
endmodule
