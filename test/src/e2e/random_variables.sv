// §18.4 Random variables: class variables declared rand or randc are
// random variables the solver randomizes, a singular variable of any
// integral or real type; §18.4.1 has a rand variable uniformly distributed
// over its range, an 8-bit one over 0 to 255 and a real one over the range
// its constraints leave, §18.4.2 a randc variable cycle through all the
// values of its declared range in a random permutation, so four
// randomizations of a 2-bit one visit each value once; §18.3's enum rule
// has an enum random variable take only a named constant; a packed
// structure declared rand is treated as an integral type, and its member
// of enum type is not held to the named constants; and an object handle
// declared rand has the object's variables and constraints solved
// concurrently with those of the object holding the handle, the handle
// itself never modified. Each line prints how many of 40 randomizations
// of the Vars object met what the rule determines and never a value the
// generator chose.
typedef enum bit [1:0] {A = 2'b00, B = 2'b11} ab_e;
typedef struct packed {
  ab_e ValidAB;
} VStructEnum;

class Inner;
  rand int v;
  constraint cv { v inside {[1:3]}; }
endclass

class Vars;
  rand bit [7:0] y;
  randc bit [1:0] c;
  rand real r;
  rand ab_e e;
  rand VStructEnum s;
  rand Inner in;
  rand bit [3:0] w;
  constraint cr { r > 0.0 && r < 2.0; }
  constraint cw { w > in.v; }
  function new();
    in = new;
  endfunction
endclass

module random_variables;
  initial begin
    Vars vars = new;
    Inner held = vars.in;
    int solved = 0, y_in_range = 0, r_in_range = 0, e_named = 0;
    int s_unnamed = 0, in_solved = 0, w_above = 0, handle_kept = 0;
    int cycles = 0;
    bit [3:0] seen;
    repeat (10) begin
      seen = 0;
      repeat (4) begin
        if (vars.randomize() == 1) solved++;
        seen[vars.c] = 1;
        if (vars.y <= 255) y_in_range++;
        if (vars.r > 0.0 && vars.r < 2.0) r_in_range++;
        if (vars.e == A || vars.e == B) e_named++;
        if (vars.s != 2'b00 && vars.s != 2'b11) s_unnamed++;
        if (vars.in.v >= 1 && vars.in.v <= 3) in_solved++;
        if (vars.w > vars.in.v) w_above++;
        if (vars.in == held) handle_kept++;
      end
      if (seen == 4'b1111) cycles++;
    end
    $display("solved %0d of 40", solved);
    $display("y within 0 to 255: %0d of 40", y_in_range);
    $display("randc c visited every value in each group of four: %0d of 10", cycles);
    $display("r within 0.0 to 2.0: %0d of 40", r_in_range);
    $display("e a named constant: %0d of 40", e_named);
    $display("s took a value its enum member does not name: %0d", s_unnamed > 0);
    $display("in.v solved under its own constraint: %0d of 40", in_solved);
    $display("w > in.v under the holder's constraint: %0d of 40", w_above);
    $display("handle in unmodified: %0d of 40", handle_kept);
    $finish;
  end
endmodule
