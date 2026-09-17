// 18.5.12: constraint guards, the clause's three examples over a D held by
// two handles a and b, and its singly linked list sorted under a guard.
class D;
  int x;
endclass

// Example 1: the guard subexpressions are joined by disjunction.
class Disjoined;
  rand int x, y;
  D a, b;
  constraint c1 { (x < y || a.x > b.x || a.x == 5) -> x + y == 10; }
endclass

// Example 2: the guard subexpressions are joined by conjunction.
class Conjoined;
  rand int x, y;
  D a, b;
  constraint c1 { (x < y && a.x > b.x && a.x == 5) -> x + y == 10; }
endclass

// Example 3: a disjunction nested in a conjunction.
class Nested;
  rand int x, y;
  D a, b;
  constraint c1 { (x < y && (a.x > b.x || a.x == 5)) -> x + y == 10; }
endclass

// The clause's SList: the guard eliminates the last node's constraint, whose
// next is null, where n < next.n would fail on the nonexistent handle.
class SList;
  rand int n;
  rand SList next;
  constraint sort { if (next != null) n < next.n; }
endclass

module constraint_guards;
  Disjoined dj;
  Conjoined cj;
  Nested ne;
  SList head, second, tail;
  D da, db;
  int ok, sums, apart, ordered, above, i;

  initial begin
    // Example 1, case 1: a.x is 5 and b is null. The disjunct a.x == 5 is
    // TRUE, so the ERROR of b.x is sifted away and the unconditional
    // constraint x + y == 10 is generated: it holds on every draw, whether
    // or not x < y.
    dj = new;
    da = new;
    da.x = 5;
    dj.a = da;
    ok = 0;
    sums = 0;
    apart = 0;
    for (i = 0; i < 64; i++) begin
      if (dj.randomize()) ok++;
      if (dj.x + dj.y == 10) sums++;
      if (dj.x >= dj.y) apart++;
    end
    $display("disjunction, a.x 5 and b null: solved %0d of 64, x + y is 10 in %0d, x at or above y in some: %0d",
             ok, sums, apart > 0);

    // Example 1, case 2: a is null. Every subexpression over a is an ERROR
    // and no disjunct is TRUE, so an error is generated and randomize()
    // fails.
    dj = new;
    db = new;
    db.x = 20;
    dj.b = db;
    ok = dj.randomize();
    $display("disjunction, a null: randomize returns %0d", ok);

    // Example 1, case 3: a.x is 10 and b.x is 20. Every guard subexpression
    // over the state is FALSE and x < y is RANDOM, so the conditional
    // constraint (x < y) -> x + y == 10 is generated, which under x < y
    // holds x + y to 10 on every draw.
    dj = new;
    da = new;
    da.x = 10;
    dj.a = da;
    dj.b = db;
    ok = 0;
    sums = 0;
    for (i = 0; i < 64; i++) begin
      if (dj.randomize() with { x < y; }) ok++;
      if (dj.x + dj.y == 10) sums++;
    end
    $display("disjunction, a.x 10 and b.x 20, under x < y: solved %0d of 64, x + y is 10 in %0d",
             ok, sums);

    // Example 2, case 1: a.x is 6 and b is null. The conjunct a.x == 5 is
    // FALSE, so the ERROR of b.x is sifted away and the constraint is
    // eliminated: x and y are drawn free, and a pair of ints sums to 10 as
    // good as never.
    cj = new;
    da = new;
    da.x = 6;
    cj.a = da;
    ok = 0;
    sums = 0;
    for (i = 0; i < 64; i++) begin
      if (cj.randomize()) ok++;
      if (cj.x + cj.y == 10) sums++;
    end
    $display("conjunction, a.x 6 and b null: solved %0d of 64, x + y is 10 in %0d",
             ok, sums);

    // Example 2, case 2: a is null, an error whatever the other conjuncts.
    cj = new;
    cj.b = db;
    ok = cj.randomize();
    $display("conjunction, a null: randomize returns %0d", ok);

    // Example 2, case 3: a.x is 5 and b.x is 2. Every guard subexpression
    // over the state is TRUE, so the conditional constraint (x < y) -> x + y
    // == 10 is generated.
    cj = new;
    da = new;
    da.x = 5;
    db = new;
    db.x = 2;
    cj.a = da;
    cj.b = db;
    ok = 0;
    sums = 0;
    for (i = 0; i < 64; i++) begin
      if (cj.randomize() with { x < y; }) ok++;
      if (cj.x + cj.y == 10) sums++;
    end
    $display("conjunction, a.x 5 and b.x 2, under x < y: solved %0d of 64, x + y is 10 in %0d",
             ok, sums);

    // Example 3, case 1: a.x is 5 and b is null. The inner disjunction is
    // (ERROR || TRUE), which is TRUE, and conjoined with the RANDOM x < y
    // gives RANDOM: the conditional constraint is generated.
    ne = new;
    ne.a = da;
    ok = 0;
    sums = 0;
    for (i = 0; i < 64; i++) begin
      if (ne.randomize() with { x < y; }) ok++;
      if (ne.x + ne.y == 10) sums++;
    end
    $display("nested, a.x 5 and b null, under x < y: solved %0d of 64, x + y is 10 in %0d",
             ok, sums);

    // Example 3, case 2: a.x is 8 and b is null. The inner disjunction is
    // (ERROR || FALSE), which is ERROR, and no conjunct is FALSE to sift it,
    // so an error is generated.
    ne = new;
    da = new;
    da.x = 8;
    ne.a = da;
    ok = ne.randomize();
    $display("nested, a.x 8 and b null: randomize returns %0d", ok);

    // Example 3, case 3: a is null, an error whatever the rest.
    ne = new;
    ne.b = db;
    ok = ne.randomize();
    $display("nested, a null: randomize returns %0d", ok);

    // The SList of three nodes: the guard next != null is TRUE on the first
    // two, whose sort constraints are generated, and FALSE on the tail,
    // whose constraint is eliminated rather than failing on the null next.
    // The three are randomized as one whole, so the values ascend on every
    // draw, and the tail, held above the second alone, draws above zero in
    // some draw where a constraint reading through the null next would not.
    head = new;
    second = new;
    tail = new;
    head.next = second;
    second.next = tail;
    ok = 0;
    ordered = 0;
    above = 0;
    for (i = 0; i < 32; i++) begin
      if (head.randomize()) ok++;
      if (head.n < second.n && second.n < tail.n) ordered++;
      if (tail.n > 0) above++;
    end
    $display("the guarded sort: solved %0d of 32, ascending in %0d, the tail above zero in some: %0d",
             ok, ordered, above > 0);
    $finish;
  end
endmodule
