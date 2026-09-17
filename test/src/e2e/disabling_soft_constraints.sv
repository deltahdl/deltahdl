// 18.5.13.2: disabling soft constraints, the clause's A, whose disable soft
// discards the lower-priority preference and leaves the later membership,
// its C, whose directive discards only the soft constraints the variable
// directly appears in, and its B, whose directive discards a preference
// that contradicts nothing so that the soft distribution after it holds.
class A;
  rand int x;
  constraint A1 { soft x == 3; }
  constraint A2 { disable soft x; }
  constraint A3 { soft x inside {1, 2}; }
endclass

// The clause's A with A3 omitted: x is left unconstrained.
class Freed;
  rand int x;
  constraint A1 { soft x == 3; }
  constraint A2 { disable soft x; }
endclass

// The clause's C over random p and q: p gates the soft q of c_1 without
// appearing in it, and c_2 prefers p.
class C;
  rand bit p;
  rand bit q;
  constraint c_1 { p -> soft q; }
  constraint c_2 { soft p; }
  constraint c_3 { disable soft p; }
endclass

class Cq;
  rand bit p;
  rand bit q;
  constraint c_1 { p -> soft q; }
  constraint c_2 { soft p; }
  constraint c_3 { disable soft q; }
endclass

class B;
  rand int x;
  constraint B1 { soft x == 5; }
  constraint B2 { disable soft x; soft x dist {5, 8}; }
endclass

// The clause's B with the directive omitted: the distribution is satisfied
// by 5 alone.
class Kept;
  rand int x;
  constraint B1 { soft x == 5; }
  constraint B3 { soft x dist {5, 8}; }
endclass

module disabling_soft_constraints;
  A a;
  Freed f;
  C c;
  Cq cq;
  B b;
  Kept k;
  int held, ones, twos, threes, sets, gated, clears, fives, i;

  initial begin
    // A: the directive discards A1, the lower-priority preference for 3,
    // and leaves A3, declared after it, so x takes 1 and 2.
    a = new;
    held = 0;
    ones = 0;
    twos = 0;
    for (i = 0; i < 64; i++) begin
      void'(a.randomize());
      if (a.x == 1 || a.x == 2) held++;
      if (a.x == 1) ones++;
      if (a.x == 2) twos++;
    end
    $display("the clause's A: x in {1, 2} in %0d of 64, both drawn: %0d", held,
             (ones > 0) && (twos > 0));

    // A without A3: the preference discarded, x is unconstrained, so a draw
    // over the whole of an int is 3 as good as never.
    f = new;
    threes = 0;
    for (i = 0; i < 64; i++) begin
      void'(f.randomize());
      if (f.x == 3) threes++;
    end
    $display("A without A3: x is 3 in %0d of 64", threes);

    // C: disable soft p discards c_2, in which p appears, and not c_1, which
    // p only gates, so p is drawn free and q is set whenever p is.
    c = new;
    sets = 0;
    gated = 0;
    for (i = 0; i < 64; i++) begin
      void'(c.randomize());
      if (c.p) sets++;
      if (!c.p || c.q) gated++;
    end
    $display("disable soft p: p set in some: %0d, q set whenever p in %0d of 64",
             sets > 0, gated);

    // C with disable soft q: c_1 is discarded and c_2 stands, so p is set
    // on every draw and q is drawn free.
    cq = new;
    sets = 0;
    clears = 0;
    for (i = 0; i < 64; i++) begin
      void'(cq.randomize());
      if (cq.p) sets++;
      if (!cq.q) clears++;
    end
    $display("disable soft q: p set in %0d of 64, q clear in some: %0d", sets,
             clears > 0);

    // B: the directive discards B1 though it contradicts nothing, so the
    // distribution after it gives 5 and 8 with equal weight.
    b = new;
    held = 0;
    fives = 0;
    for (i = 0; i < 64; i++) begin
      void'(b.randomize());
      if (b.x == 5 || b.x == 8) held++;
      if (b.x == 5) fives++;
    end
    $display("the clause's B: x in {5, 8} in %0d of 64, 5 in near half: %0d", held,
             (fives >= 16) && (fives <= 48));

    // B without the directive: the distribution is satisfied by 5, which
    // the preference holds x to.
    k = new;
    fives = 0;
    for (i = 0; i < 64; i++) begin
      void'(k.randomize());
      if (k.x == 5) fives++;
    end
    $display("B without the directive: x is 5 in %0d of 64", fives);
    $finish;
  end
endmodule
