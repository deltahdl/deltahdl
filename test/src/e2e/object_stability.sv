// IEEE 1800-2023 §18.14.3: the randomize() built into every class exhibits
// object stability, the calls to randomize() on one instance being
// independent of the calls on other instances and of calls to other
// randomize functions. In the clause's example c1.x and c2.y are independent
// of each other, a z = $random between the two calls changes neither, and
// each instance has a unique source of random values that can be seeded
// independently, its seed taken from the parent thread when the instance is
// created. So the example run again with a $random, a $urandom and a
// std::randomize() between the calls returns the same c1.x and c2.y; c1.x is
// the same after five more calls on c2; two instances seeded alike draw
// alike and an instance seeded again replays; and an instance seeded by hand
// with the parent thread's next value draws as the one created there.
module object_stability;
  class C1;
    rand integer x;
  endclass

  class C2;
    rand integer y;
  endclass

  C1 c1, d1;
  C2 c2;
  process p;
  integer z, xa, ya, xb, yb, xc, xd, xe, sa[4], sb[4], sc[4];
  int unsigned seedv, k;
  int i, v, ok, between, others, alike, replayed, from_parent;

  initial begin
    p = process::self();
    p.srandom(9);
    c1 = new();
    c2 = new();
    void'(c1.randomize());
    void'(c2.randomize());
    xa = c1.x;
    ya = c2.y;
    p.srandom(9);
    c1 = new();
    c2 = new();
    void'(c1.randomize());
    z = $random;
    k = $urandom;
    ok = std::randomize(v);
    void'(c2.randomize());
    xb = c1.x;
    yb = c2.y;
    between = 0;
    if (xa == xb) between++;
    if (ya == yb) between++;
    $display("example: c1.x and c2.y with a $random, a $urandom and a std::randomize() between the calls agree with the run without in %0d of 2",
             between);

    p.srandom(9);
    c1 = new();
    c2 = new();
    for (i = 0; i < 5; i++) void'(c2.randomize());
    void'(c1.randomize());
    xc = c1.x;
    others = xc == xa;
    c1.srandom(3);
    d1 = new();
    d1.srandom(3);
    for (i = 0; i < 4; i++) begin void'(c1.randomize()); sa[i] = c1.x; end
    for (i = 0; i < 4; i++) begin void'(d1.randomize()); sb[i] = d1.x; end
    c1.srandom(3);
    for (i = 0; i < 4; i++) begin void'(c1.randomize()); sc[i] = c1.x; end
    alike = 0;
    replayed = 0;
    for (i = 0; i < 4; i++) if (sa[i] == sb[i]) alike++;
    for (i = 0; i < 4; i++) if (sa[i] == sc[i]) replayed++;
    $display("independence: c1.x after five calls on c2 agrees: %0d, two instances seeded 3 draw alike in %0d of 4, c1 seeded 3 again replays in %0d of 4",
             others, alike, replayed);

    p.srandom(9);
    c1 = new();
    void'(c1.randomize());
    xd = c1.x;
    p.srandom(9);
    seedv = $urandom;
    d1 = new();
    d1.srandom(seedv);
    void'(d1.randomize());
    xe = d1.x;
    from_parent = xd == xe;
    $display("seed: an instance seeded by hand with the parent thread's next value draws as the one created there: %0d",
             from_parent);
    $finish;
  end
endmodule
