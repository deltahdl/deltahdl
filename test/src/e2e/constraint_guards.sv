class D;
  int x;
endclass

class Disjoined;
  rand int x, y;
  D a, b;
  constraint c1 { (x < y || a.x > b.x || a.x == 5) -> x + y == 10; }
endclass

class Conjoined;
  rand int x, y;
  D a, b;
  constraint c1 { (x < y && a.x > b.x && a.x == 5) -> x + y == 10; }
endclass

class Nested;
  rand int x, y;
  D a, b;
  constraint c1 { (x < y && (a.x > b.x || a.x == 5)) -> x + y == 10; }
endclass

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

    dj = new;
    db = new;
    db.x = 20;
    dj.b = db;
    ok = dj.randomize();
    $display("disjunction, a null: randomize returns %0d", ok);

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

    cj = new;
    cj.b = db;
    ok = cj.randomize();
    $display("conjunction, a null: randomize returns %0d", ok);

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

    ne = new;
    da = new;
    da.x = 8;
    ne.a = da;
    ok = ne.randomize();
    $display("nested, a.x 8 and b null: randomize returns %0d", ok);

    ne = new;
    ne.b = db;
    ok = ne.randomize();
    $display("nested, a null: randomize returns %0d", ok);

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
