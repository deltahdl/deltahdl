// IEEE 1800-2023 §18.15: each object maintains its own internal RNG, used
// exclusively by its randomize() method, so objects are randomized
// independently of each other and of calls to other system randomization
// functions; an object's RNG is seeded at creation with the next value of the
// creating thread's RNG, hierarchical object seeding, and can be seeded by
// hand with srandom() either in a class method or outside the class. So two
// Packets whose new(seed) calls this.srandom(seed) with 200 draw alike
// though created at different points of the thread, and a $urandom and a
// $random between the draws change nothing; a Packet re-seeded from outside
// with 300 draws as one created with 300; srandom() in new() sets the seed
// before any member is randomized, so a Packet that randomizes itself inside
// new() after the srandom holds the first draw of one that does not; and a
// Plain object without a seeding constructor draws as one seeded by hand
// with the value the creating thread would have drawn next.
module manually_seeding_randomize;
  class Packet;
    rand bit [15:0] header;
    function new(int seed, bit draw = 0);
      this.srandom(seed);
      if (draw) void'(this.randomize());
    endfunction
  endclass

  class Plain;
    rand bit [15:0] header;
  endclass

  Packet p, q, r;
  Plain a, b;
  process pr;
  integer z;
  int unsigned k, seedv;
  bit [15:0] h1[4], h2[4], h3[4], h4[4], first;
  int i, alike, unmoved, external, in_new, hierarchical;

  initial begin
    pr = process::self();
    pr.srandom(9);
    p = new(200);
    for (i = 0; i < 4; i++) begin void'(p.randomize()); h1[i] = p.header; end
    first = h1[0];
    for (i = 0; i < 5; i++) k = $urandom;
    q = new(200);
    for (i = 0; i < 4; i++) begin void'(q.randomize()); h2[i] = q.header; end
    alike = 0;
    for (i = 0; i < 4; i++) if (h1[i] == h2[i]) alike++;
    p = new(200);
    for (i = 0; i < 4; i++) begin k = $urandom; z = $random; void'(p.randomize()); h3[i] = p.header; end
    unmoved = 0;
    for (i = 0; i < 4; i++) if (h1[i] == h3[i]) unmoved++;
    $display("internal: two Packets created with seed 200 draw alike in %0d of 4, a $urandom and a $random before each draw change nothing in %0d of 4",
             alike, unmoved);

    p.srandom(300);
    for (i = 0; i < 4; i++) begin void'(p.randomize()); h3[i] = p.header; end
    r = new(300);
    for (i = 0; i < 4; i++) begin void'(r.randomize()); h4[i] = r.header; end
    external = 0;
    for (i = 0; i < 4; i++) if (h3[i] == h4[i]) external++;
    $display("external: p re-seeded with 300 draws as a Packet created with seed 300 in %0d of 4", external);

    q = new(200, 1);
    in_new = q.header == first;
    $display("new: a Packet randomized inside new() after srandom(200) holds the first draw of one created with 200: %0d", in_new);

    pr.srandom(9);
    a = new;
    for (i = 0; i < 4; i++) begin void'(a.randomize()); h1[i] = a.header; end
    pr.srandom(9);
    seedv = $urandom;
    b = new;
    b.srandom(seedv);
    for (i = 0; i < 4; i++) begin void'(b.randomize()); h2[i] = b.header; end
    hierarchical = 0;
    for (i = 0; i < 4; i++) if (h1[i] == h2[i]) hierarchical++;
    $display("hierarchical: a Plain object seeded by hand with the creating thread's next value draws as one created there in %0d of 4", hierarchical);
    $finish;
  end
endmodule
