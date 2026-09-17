// 18.10: dynamic constraint modification: the four ways the clause lists
// of changing what randomize() solves without changing the class. An
// implication or if-else predicated on a state variable, a block turned
// off through constraint_mode() and so ignored by randomize(), a variable
// turned off through rand_mode() and so a state variable to the solver,
// and a dist whose weights are state variables, changed between calls to
// move the probability of each value.
class Channel;
  rand bit [7:0] len;
  rand int sel;
  rand int base, top;
  int fast = 0;
  int w_one = 1, w_two = 1;
  constraint speed { if (fast) len < 16; else len >= 16; }
  constraint floor { fast -> len > 3; }
  constraint cap { len < 200; }
  constraint pick { sel dist { 1 := w_one, 2 := w_two }; }
  constraint order { top > base; top < base + 8; }
endclass

module dynamic_constraint_modification;
  Channel c;
  int i, short_draws, long_draws, high, near, ones, twos;

  initial begin
    c = new;
    // Predicated constraints: the state fast selects which branch of the
    // if-else and whether the implication binds, so with fast set len lies
    // in (3, 16) on every draw and with it clear at or above 16.
    short_draws = 0;
    long_draws = 0;
    c.fast = 1;
    for (i = 0; i < 32; i++) begin
      void'(c.randomize());
      if (c.len > 3 && c.len < 16) short_draws++;
    end
    c.fast = 0;
    for (i = 0; i < 32; i++) begin
      void'(c.randomize());
      if (c.len >= 16) long_draws++;
    end
    $display("predicated: fast draws len in (3, 16) in %0d of 32, slow draws at or above 16 in %0d of 32",
             short_draws, long_draws);

    // A block turned off is ignored by randomize(): with cap off, len is
    // drawn at or above 200 in some of 64 draws, and with it back on in
    // none of 64.
    high = 0;
    c.cap.constraint_mode(0);
    for (i = 0; i < 64; i++) begin
      void'(c.randomize());
      if (c.len >= 200) high++;
    end
    $display("constraint_mode: cap off, len at or above 200 in some of 64: %0d", high > 0);
    high = 0;
    c.cap.constraint_mode(1);
    for (i = 0; i < 64; i++) begin
      void'(c.randomize());
      if (c.len >= 200) high++;
    end
    $display("constraint_mode: cap on, len at or above 200 in %0d of 64", high);

    // A variable turned off is a state variable to the solver: base held
    // at 1000 leaves top drawn in (1000, 1008) on every call.
    near = 0;
    c.base = 1000;
    c.base.rand_mode(0);
    for (i = 0; i < 32; i++) begin
      void'(c.randomize());
      if (c.base == 1000 && c.top > 1000 && c.top < 1008) near++;
    end
    $display("rand_mode: base held, top in (1000, 1008) in %0d of 32", near);

    // The weights of a dist are state variables read at each call: at 9:1
    // ones outnumber twos over 64 draws, and at 1:9 twos outnumber ones.
    ones = 0;
    twos = 0;
    c.w_one = 9;
    c.w_two = 1;
    for (i = 0; i < 64; i++) begin
      void'(c.randomize());
      if (c.sel == 1) ones++;
      if (c.sel == 2) twos++;
    end
    $display("dist: weights 9:1 draw only 1 and 2: %0d, ones outnumber twos: %0d",
             ones + twos == 64, ones > twos);
    ones = 0;
    twos = 0;
    c.w_one = 1;
    c.w_two = 9;
    for (i = 0; i < 64; i++) begin
      void'(c.randomize());
      if (c.sel == 1) ones++;
      if (c.sel == 2) twos++;
    end
    $display("dist: weights 1:9 draw only 1 and 2: %0d, twos outnumber ones: %0d",
             ones + twos == 64, twos > ones);
    $finish;
  end
endmodule
