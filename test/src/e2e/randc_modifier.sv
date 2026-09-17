// §18.4.2 Randc modifier: a variable declared randc is random-cyclic,
// cycling through all the values of its declared range in a random
// permutation, randomize() computing an initial permutation and returning
// its values in order on successive calls, and after the last computing a
// new one, so that no value repeats within an iteration; the permutation
// is recomputed whenever the constraints on the variable change, so that a
// constraint block enabled after some draws confines the next ones; an
// implementation may cap the size of a randc variable but at no less than
// 8 bits, so an 8-bit one visits all 256 values in 256 calls; and a randc
// variable declared static keeps its cyclic state with the class, so
// randomize() through any instance takes the next value of the one
// sequence. Each line prints whether the draws met what the rule
// determines and never a value the generator chose.
class Cyclic;
  randc bit [1:0] y;
endclass

class Wide;
  randc bit [7:0] z;
endclass

class Changing;
  randc bit [1:0] c;
  constraint hi { c >= 2; }
endclass

class Shared;
  static randc bit [1:0] s;
endclass

module randc_modifier;
  bit [3:0] seen;
  bit [255:0] visited;
  int groups = 0, distinct = 0, confined = 0;
  initial begin
    Cyclic cy = new;
    Wide w = new;
    Changing ch = new;
    Shared s1 = new;
    Shared s2 = new;
    repeat (3) begin
      seen = 0;
      repeat (4) begin
        void'(cy.randomize());
        seen[cy.y] = 1;
      end
      if (seen == 4'b1111) groups++;
    end
    $display("each of three iterations of y visits all four values: %0d", groups == 3);
    repeat (256) begin
      void'(w.randomize());
      visited[w.z] = 1;
    end
    for (int k = 0; k < 256; k++) if (visited[k]) distinct++;
    $display("256 calls visit all 256 values of the 8-bit z: %0d", distinct == 256);
    ch.hi.constraint_mode(0);
    seen = 0;
    repeat (4) begin
      void'(ch.randomize());
      seen[ch.c] = 1;
    end
    $display("with hi off an iteration of c visits all four values: %0d", seen == 4'b1111);
    ch.hi.constraint_mode(1);
    seen = 0;
    repeat (4) begin
      void'(ch.randomize());
      seen[ch.c] = 1;
      if (ch.c >= 2) confined++;
    end
    $display("with hi on the recomputed permutation holds c to 2 and 3: %0d", confined == 4 && seen == 4'b1100);
    seen = 0;
    void'(s1.randomize()); seen[s1.s] = 1;
    void'(s2.randomize()); seen[s2.s] = 1;
    void'(s1.randomize()); seen[s1.s] = 1;
    void'(s2.randomize()); seen[s2.s] = 1;
    $display("a static randc cycles through one sequence across instances: %0d", seen == 4'b1111);
    $finish;
  end
endmodule
