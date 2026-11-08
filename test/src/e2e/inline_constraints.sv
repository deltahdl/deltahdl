class SimpleSum;
  rand bit [7:0] x, y, z;
  constraint c { z == x + y; }
endclass

class C1;
  rand integer x;
endclass

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

  task InlineConstraintDemo(SimpleSum p);
    int success;
    success = p.randomize() with { x < y; };
    if (success == 1) ordered++;
  endtask

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
