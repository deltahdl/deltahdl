class A;
  rand int x;
  constraint A1 { soft x == 3; }
  constraint A2 { disable soft x; }
  constraint A3 { soft x inside {1, 2}; }
endclass

class Freed;
  rand int x;
  constraint A1 { soft x == 3; }
  constraint A2 { disable soft x; }
endclass

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

    f = new;
    threes = 0;
    for (i = 0; i < 64; i++) begin
      void'(f.randomize());
      if (f.x == 3) threes++;
    end
    $display("A without A3: x is 3 in %0d of 64", threes);

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
