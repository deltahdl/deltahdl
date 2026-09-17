// §18.5.1 External constraint blocks: a constraint prototype declared in a
// class, in the implicit form of a name alone or the explicit form
// prefixed by extern, specifies that the class has a constraint of that
// name without giving its block; either is completed by an external
// constraint block written after the class in the same scope and named
// through the class scope resolution operator. An implicit prototype
// without an external block is an empty constraint, one with no effect on
// randomization, as a block holding the constant 1 would be. The C here
// carries both forms, completed outside the class to hold x inside -4, 5
// and 7 and to at least 0, so every draw is 5 or 7; the completed block
// keeps its prototype's name, so turning proto1 off frees x to any value
// at least 0; and the E declaring an uncompleted implicit prototype
// randomizes as if it had no constraint, its 8-bit y drawn freely.
class C;
  rand int x;
  constraint proto1;
  extern constraint proto2;
endclass

constraint C::proto1 { x inside {-4, 5, 7}; }
constraint C::proto2 { x >= 0; }

class E;
  rand bit [7:0] y;
  constraint empty;
endclass

module external_constraint_blocks;
  int both = 0, at_least_zero = 0, freed = 0, solved = 0;
  bit [255:0] seen = 0;
  int distinct = 0;
  initial begin
    C c = new;
    E e = new;
    repeat (32) begin
      void'(c.randomize());
      if (c.x == 5 || c.x == 7) both++;
    end
    $display("both completed prototypes hold, x is 5 or 7: %0d of 32", both);
    c.proto1.constraint_mode(0);
    repeat (32) begin
      void'(c.randomize());
      if (c.x >= 0) at_least_zero++;
      if (c.x != 5 && c.x != 7) freed++;
    end
    $display("with proto1 off by its name x is at least 0: %0d of 32, and free of 5 and 7: %0d",
             at_least_zero, freed > 0);
    repeat (64) begin
      if (e.randomize()) solved++;
      seen[e.y] = 1;
    end
    for (int i = 0; i < 256; i++) if (seen[i]) distinct++;
    $display("an uncompleted implicit prototype is empty: randomize() succeeds %0d of 64 times, y takes more than one value: %0d",
             solved, distinct > 1);
    $finish;
  end
endmodule
