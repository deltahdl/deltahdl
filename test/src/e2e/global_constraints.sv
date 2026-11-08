class Leaf;
  rand bit [7:0] v;
endclass

class Heap extends Leaf;
  rand Leaf left;
  rand Leaf right;
  constraint heapcond { left.v <= v; right.v > v; }
  function new();
    left = new;
    right = new;
  endfunction
endclass

module global_constraints;
  int ordered = 0, nested = 0, held = 0, first_left = -1, first_right = -1;
  int left_varies = 0, right_varies = 0;
  initial begin
    static Heap h = new;
    static Heap outer = new;
    static Heap inner = new;
    static Heap fixed = new;
    Leaf keep;
    repeat (128) begin
      void'(h.randomize());
      if (h.left.v <= h.v && h.right.v > h.v) ordered++;
      if (first_left < 0) first_left = h.left.v;
      else if (h.left.v != first_left) left_varies = 1;
      if (first_right < 0) first_right = h.right.v;
      else if (h.right.v != first_right) right_varies = 1;
    end
    outer.left = inner;
    repeat (64) begin
      void'(outer.randomize());
      if (outer.left.v <= outer.v && outer.right.v > outer.v &&
          inner.left.v <= inner.v && inner.right.v > inner.v)
        nested++;
    end
    keep = fixed.right;
    keep.v = 200;
    fixed.right.rand_mode(0);
    repeat (64) begin
      void'(fixed.randomize());
      if (keep.v == 200 && fixed.v < 200 && fixed.left.v <= fixed.v) held++;
    end
    $display("both global constraints hold: %0d of 128", ordered);
    $display("the leaves are drawn with the node: %0d %0d", left_varies,
             right_varies);
    $display("a heap node under a heap node holds its own: %0d of 64", nested);
    $display("an inactive subtree is a state variable: %0d of 64", held);
    $finish;
  end
endmodule
