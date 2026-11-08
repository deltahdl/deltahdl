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

class Pick;
  rand int v;
  constraint c { soft v == 10; }
endclass

class Ext;
  rand int v;
  constraint early { soft v == 1; }
  constraint late;
endclass

constraint Ext::late { soft v == 2; }

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

    k = new;
    ok = k.randomize() with { soft v == 20; };
    $display("inline over the class: solved %0d, v is %0d", ok, k.v);

    x = new;
    ok = x.randomize();
    $display("the external block at its prototype's place: solved %0d, v is %0d",
             ok, x.v);

    b = new;
    b.e = new;
    b.l = new;
    ok = b.randomize();
    $display("the container and the later handle: solved %0d, e.v is %0d, l.v is %0d",
             ok, b.e.v, b.l.v);
    $finish;
  end
endmodule
