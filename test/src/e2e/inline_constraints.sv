// 18.7: in-line constraints, the randomize() with construct declaring
// constraints at the point of the call, applied along with the object's
// own, and the resolution of the names in its block: a name resolving in
// the class of the object first, then in the scope containing the call,
// and, in a restricted block, only the listed names resolving in the
// object.
class SimpleSum;
  rand bit [7:0] x, y, z;
  constraint c { z == x + y; }
endclass

class C1;
  rand integer x;
endclass

// The clause's C2: its x and y are members, and doit's x and z arguments;
// in the block x is C1's, hiding the member and the argument, y the
// member, and z the argument. The clause's x < y + z is held from below by
// y as well, so that the y the block read shows in the draws.
class C2;
  integer x;
  integer y;
  function int doit(C1 f, integer x, integer z);
    return f.randomize() with { x < y + z; x >= y; };
  endfunction
endclass

class C;
  rand integer x;
  rand integer y;
endclass

module inline_constraints;
  SimpleSum p;
  C1 f;
  C2 c2;
  C obj;
  int success, ordered, summed, below, i, sum;

  // The clause's demo: the inline x < y is applied with the class's c.
  task InlineConstraintDemo(SimpleSum p);
    int success;
    success = p.randomize() with { x < y; };
    if (success == 1) ordered++;
  endtask

  // The clause's restricted block: only x resolves into obj, so y is the
  // argument.
  function int F(C obj, integer y);
    F = obj.randomize() with (x) { x < y; };
  endfunction

  initial begin
    p = new;
    ordered = 0;
    summed = 0;
    below = 0;
    for (i = 0; i < 64; i++) begin
      InlineConstraintDemo(p);
      sum = (p.x + p.y) & 255;
      if (p.z == sum) summed++;
      if (p.x < p.y) below++;
    end
    $display("the demo: success %0d of 64, z is x + y in %0d, x below y in %0d",
             ordered, summed, below);

    // C2's doit: f.x from y, the member 10, below y + z, z the argument 5,
    // on every draw, whatever the argument x, which the block's x hides.
    f = new;
    c2 = new;
    c2.x = -1000;
    c2.y = 10;
    success = 0;
    below = 0;
    for (i = 0; i < 64; i++) begin
      if (c2.doit(f, -1000, 5) == 1) success++;
      if (f.x >= 10 && f.x < 15) below++;
    end
    $display("doit: success %0d of 64, f.x from 10 below 15 in %0d", success,
             below);

    // F's restricted block: obj.x below the argument 20 on every draw, y
    // never binding into obj though obj has a y.
    obj = new;
    success = 0;
    below = 0;
    for (i = 0; i < 64; i++) begin
      if (F(obj, 20) == 1) success++;
      if (obj.x < 20) below++;
    end
    $display("F: success %0d of 64, obj.x below 20 in %0d", success, below);
    $finish;
  end
endmodule
