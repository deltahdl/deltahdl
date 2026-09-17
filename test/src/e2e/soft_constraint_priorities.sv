// 18.5.13.1: soft constraint priorities, the clause's example of a D2
// holding two D1 and a B1, randomized with an inline block, beside the
// rules taken one at a time: an inline block over the class, an external
// block at its prototype's place, and a container over the objects it
// holds, in the order of their handles.
class B1;
  rand int x;
  constraint a { soft x > 10; soft x < 100; }
endclass

class D1 extends B1;
  constraint b { soft x inside {[5:9]}; }
endclass

class B2;
  rand int y;
  constraint c { soft y > 10; }
endclass

class D2 extends B2;
  constraint d { soft y inside {[5:9]}; }
  constraint e;
  rand D1 p1;
  rand B1 p2;
  rand D1 p3;
  constraint f { soft p1.x < p2.x; }
endclass

constraint D2::e { soft y > 100; }

// A preference of the class against one of the inline block.
class Pick;
  rand int v;
  constraint c { soft v == 10; }
endclass

// A prototype declared after the block it outranks, completed by an
// external block.
class Ext;
  rand int v;
  constraint early { soft v == 1; }
  constraint late;
endclass

constraint Ext::late { soft v == 2; }

// Two contained objects preferring different values, tied together by
// their container.
class Early;
  rand int v;
  constraint c { soft v == 1; }
endclass

class Late;
  rand int v;
  constraint c { soft v == 2; }
endclass

class Both;
  rand Early e;
  rand Late l;
  constraint tie { soft e.v == l.v; }
endclass

module soft_constraint_priorities;
  D2 d;
  Pick k;
  Ext x;
  Both b;
  int ok, picked, ordered, third, i;

  initial begin
    // The clause's example. Highest to lowest: i2, i1, f1, e1, d1, c1,
    // p3.b1, p3.a2, p3.a1, p2.a2, p2.a1, p1.b1, p1.a2, p1.a1. Reinstated in
    // that order while the set stays satisfiable: i2 and i1 hold y to one of
    // 10, 20 and 30 below p1.x; e1 and d1 contradict i1 and are discarded;
    // c1 leaves 20 and 30; p3 keeps b1 and a2 and loses a1; p2 keeps both;
    // p1 loses b1, no value of 5 to 9 lying above y, and keeps a2 and a1.
    d = new;
    d.p1 = new;
    d.p2 = new;
    d.p3 = new;
    ok = 0;
    picked = 0;
    ordered = 0;
    third = 0;
    for (i = 0; i < 16; i++) begin
      if (d.randomize() with { soft y inside {10, 20, 30}; soft y < p1.x; })
        ok++;
      if (d.y == 20 || d.y == 30) picked++;
      if (d.y < d.p1.x && d.p1.x < d.p2.x && d.p2.x < 100) ordered++;
      if (d.p3.x >= 5 && d.p3.x <= 9) third++;
    end
    $display("the clause's example: solved %0d of 16, y in {20, 30} in %0d, y < p1.x < p2.x < 100 in %0d, p3.x in [5:9] in %0d",
             ok, picked, ordered, third);

    // An inline block outranks the class being randomized.
    k = new;
    ok = k.randomize() with { soft v == 20; };
    $display("inline over the class: solved %0d, v is %0d", ok, k.v);

    // An external block has the priority of its prototype's place, here
    // after the block it contradicts.
    x = new;
    ok = x.randomize();
    $display("the external block at its prototype's place: solved %0d, v is %0d",
             ok, x.v);

    // The container outranks its objects, and the object whose handle is
    // declared later outranks the one before it, so both take the later's
    // value.
    b = new;
    b.e = new;
    b.l = new;
    ok = b.randomize();
    $display("the container and the later handle: solved %0d, e.v is %0d, l.v is %0d",
             ok, b.e.v, b.l.v);
    $finish;
  end
endmodule
