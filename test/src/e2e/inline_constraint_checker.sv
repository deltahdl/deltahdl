// 18.11.1: the inline constraint checker: randomize() on a class with no
// random variables assigns nothing and returns 1 where every constraint
// is satisfied and 0 otherwise, and the special argument null makes every
// member a state variable for the call, so randomize(null) checks the
// constraints against the current values, the rand members included, and
// draws nothing.
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
    // The clause's call with x < v and y > w holding: 1, nothing drawn.
    a.x = 10; a.v = 20; a.y = 30; a.w = 5;
    success = a.randomize(null);
    kept = a.x == 10 && a.v == 20 && a.y == 30 && a.w == 5;
    $display("null with the relation true: returns %0d, values kept: %0d", success, kept);

    // With v below x the relation is false: 0, and still nothing drawn,
    // the rand x and y being state variables for the call.
    a.v = 5;
    success = a.randomize(null);
    kept = a.x == 10 && a.v == 5 && a.y == 30 && a.w == 5;
    $display("null with the relation false: returns %0d, values kept: %0d", success, kept);

    // A class with no random variables: randomize() is a checker of its
    // own accord, 1 with p < q and 0 with it false, p and q untouched.
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
