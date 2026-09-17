// 18.6.3: the behavior of the randomization methods: a static random
// variable shared by every instance and changed in all of them by each
// call, a failing randomize() leaving the variables at their previous
// values and post_randomize() uncalled, and the object random stability
// randomize() implements, an object's RNG seeded by srandom().
class Shared;
  static rand bit [7:0] v;
  rand bit [7:0] own;
endclass

class Fallible;
  rand bit [7:0] x;
  rand bit [7:0] y;
  int ceiling = 255;
  int post_calls = 0;
  constraint bounded { x <= ceiling; }
  function void post_randomize();
    post_calls++;
  endfunction
endclass

class Seeded;
  rand bit [15:0] a;
  rand bit [15:0] b;
endclass

module randomization_behavior;
  Shared s1, s2;
  Fallible fa;
  Seeded p, q, r;
  int ok, agree, changed, i, kept_x, kept_y, same, differ;

  initial begin
    // The static v is one storage: after either instance is randomized both
    // read the same value, and a call on the other changes it for both.
    s1 = new;
    s2 = new;
    agree = 0;
    changed = 0;
    for (i = 0; i < 32; i++) begin
      void'(s1.randomize());
      if (s1.v == s2.v) agree++;
      kept_x = s2.v;
      void'(s2.randomize());
      if (s1.v == s2.v) agree++;
      if (s1.v != kept_x) changed++;
    end
    $display("static v: instances agree in %0d of 64 reads, a call on the other changed it in some: %0d",
             agree, changed > 0);

    // A failing call: with the ceiling at 0 no x lies at or below it and
    // above 0, so the constraints are infeasible, x and y retain their
    // previous values and post_randomize() is not called.
    fa = new;
    ok = fa.randomize();
    kept_x = fa.x;
    kept_y = fa.y;
    fa.ceiling = 0;
    ok = fa.randomize() with { x > 0; };
    $display("infeasible: randomize returns %0d, x and y retained: %0d, post_randomize %0d",
             ok, (fa.x == kept_x) && (fa.y == kept_y), fa.post_calls);

    // Object random stability: two objects seeded alike draw the same
    // sequence, and one seeded otherwise draws another.
    p = new;
    q = new;
    r = new;
    p.srandom(7);
    q.srandom(7);
    r.srandom(8);
    same = 0;
    differ = 0;
    for (i = 0; i < 8; i++) begin
      void'(p.randomize());
      void'(q.randomize());
      void'(r.randomize());
      if (p.a == q.a && p.b == q.b) same++;
      if (p.a != r.a || p.b != r.b) differ++;
    end
    $display("seeded alike: the same draws in %0d of 8, seeded otherwise: other draws in some: %0d",
             same, differ > 0);
    $finish;
  end
endmodule
