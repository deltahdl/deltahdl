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
    static Cyclic cy = new;
    static Wide w = new;
    static Changing ch = new;
    static Shared s1 = new;
    static Shared s2 = new;
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
