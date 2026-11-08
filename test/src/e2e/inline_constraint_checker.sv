class CA;
  rand byte x, y;
  byte v, w;
  constraint c1 { x < v && y > w; }
endclass

class Ordered;
  byte p, q;
  constraint order { p < q; }
endclass

module inline_constraint_checker;
  CA a;
  Ordered o;
  int success, kept;

  initial begin
    a = new;
    a.x = 10; a.v = 20; a.y = 30; a.w = 5;
    success = a.randomize(null);
    kept = a.x == 10 && a.v == 20 && a.y == 30 && a.w == 5;
    $display("null with the relation true: returns %0d, values kept: %0d", success, kept);

    a.v = 5;
    success = a.randomize(null);
    kept = a.x == 10 && a.v == 5 && a.y == 30 && a.w == 5;
    $display("null with the relation false: returns %0d, values kept: %0d", success, kept);

    o = new;
    o.p = 1; o.q = 2;
    success = o.randomize();
    kept = o.p == 1 && o.q == 2;
    $display("no random variables, p < q: returns %0d, values kept: %0d", success, kept);
    o.p = 3;
    success = o.randomize();
    kept = o.p == 3 && o.q == 2;
    $display("no random variables, p > q: returns %0d, values kept: %0d", success, kept);
    $finish;
  end
endmodule
