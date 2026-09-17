// §18.5.8 global constraints: when an object member of a class is declared
// rand, all of its constraints and random variables are randomized
// simultaneously along with the other class variables and constraints, and
// a constraint expression involving random variables from other objects is a
// global constraint. The objects randomized as a whole are the object that
// invoked randomize() and, recursively, the rand and active objects it
// contains; the active constraints and the active random variables are
// those of that set, and every other variable reference is a state variable
// whose current value is a constant. The Leaf and the Heap below are the
// clause's A and B, a leaf holding a byte v and a heap node extending it
// with a rand left and right subtree under heapcond, left.v <= v and
// right.v > v. Over 128 draws of a heap node over two leaves both global
// constraints hold at once, and the leaves' values are drawn with the node's,
// each varying across the draws; over 64 draws of a heap node whose left
// subtree is a heap node in turn, both nodes' heapcond hold at once, the
// inner node reached recursively; and over 64 draws of a heap node whose
// right subtree is made inactive through rand_mode() after being set to 200,
// the right leaf keeps 200 while the node's v is drawn below it and its left
// leaf at or below the node's. Each line prints whether the count met what
// the clause determines and never a value the generator chose.
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
    Heap h = new;
    Heap outer = new;
    Heap inner = new;
    Heap fixed = new;
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
