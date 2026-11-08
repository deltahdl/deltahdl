package limits;
  parameter int a = 30;
endpackage

class C;
  rand integer x;
endclass

class Holder;
  rand integer x;
  int limit = 12;
  function int bound(C obj);
    return obj.randomize() with { x < local::this.limit; x >= 0; };
  endfunction
endclass

module local_scope_resolution;
  import limits::*;
  C obj;
  Holder h;
  int success, below, i;

  function int F(C obj, integer x);
    F = obj.randomize() with { x < local::x; x >= 0; };
  endfunction

  initial begin
    obj = new;
    success = 0;
    below = 0;
    for (i = 0; i < 64; i++) begin
      if (F(obj, 40) == 1) success++;
      if (obj.x >= 0 && obj.x < 40) below++;
    end
    $display("F: success %0d of 64, obj.x from 0 below the argument 40 in %0d",
             success, below);

    begin
      static integer x = 20;
      success = 0;
      below = 0;
      for (i = 0; i < 64; i++) begin
        if (obj.randomize() with { x < local::x; x >= 0; } == 1) success++;
        if (obj.x >= 0 && obj.x < 20) below++;
      end
      $display("a local x: success %0d of 64, obj.x from 0 below the local 20 in %0d",
               success, below);
    end

    success = 0;
    below = 0;
    for (i = 0; i < 64; i++) begin
      if (obj.randomize() with { x < local::a; x >= 0; } == 1) success++;
      if (obj.x >= 0 && obj.x < 30) below++;
    end
    $display("an imported a: success %0d of 64, obj.x from 0 below the imported 30 in %0d",
             success, below);

    h = new;
    success = 0;
    below = 0;
    for (i = 0; i < 64; i++) begin
      if (h.bound(obj) == 1) success++;
      if (obj.x >= 0 && obj.x < 12) below++;
    end
    $display("local::this: success %0d of 64, obj.x from 0 below the holder's 12 in %0d",
             success, below);
    $finish;
  end
endmodule
