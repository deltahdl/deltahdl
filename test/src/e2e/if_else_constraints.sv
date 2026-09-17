// §18.5.6 If–else constraints: if (expression) constraint_set [else
// constraint_set] holds every constraint of the first set where the
// expression, any integral or real expression, is true and every
// constraint of the optional else set otherwise, and the form is equivalent
// to implications, so the condition and the sets are interdependent and
// constrain each other. An else omitted from a nested if sequence goes with
// the closest previous if that lacks one. The Sized here is the clause's
// example, an if with an else if implying len below 10 when mode is little
// and above 100 when big; the Fixed holds len to 50, which leaves mode
// neither little nor big; the Nested is the clause's dangling else, whose
// else belongs to the inner if, so big leaves len unconstrained, little
// holds it below 10 and other above 100; the Realed selects k on a real r;
// and the Braced holds an unnamed set of two relations on one side and a
// single relation on the other.
typedef enum {little, big, other} mode_t;

class Sized;
  rand mode_t mode;
  rand int len;
  constraint range { len >= 0; len <= 200; }
  constraint by_mode {
    if (mode == little)
      len < 10;
    else if (mode == big)
      len > 100;
  }
endclass

class Fixed;
  rand mode_t mode;
  rand int len;
  constraint mid { len == 50; }
  constraint by_mode {
    if (mode == little)
      len < 10;
    else if (mode == big)
      len > 100;
  }
endclass

class Nested;
  rand mode_t mode;
  rand int len;
  constraint range { len >= 0; len <= 200; }
  constraint by_mode {
    if (mode != big)
      if (mode == little)
        len < 10;
      else
        len > 100;
  }
endclass

class Realed;
  rand real r;
  rand int k;
  constraint pick { r dist { 0.5 := 1, 1.5 := 1 }; }
  constraint by_r {
    if (r > 1.0)
      k == 2;
    else
      k == 3;
  }
endclass

class Braced;
  rand bit [3:0] x;
  rand bit [3:0] y;
  constraint c {
    if (x > 7) { y > 7; y < 12; }
    else y < 4;
  }
endclass

module if_else_constraints;
  int selected = 0, littles = 0, bigs = 0, others = 0;
  int left_other = 0, nested = 0, n_littles = 0, n_bigs = 0, n_others = 0;
  int n_bigs_low = 0, realed = 0, halves = 0, braced = 0, highs = 0;
  initial begin
    Sized sz = new;
    Fixed fx = new;
    Nested ns = new;
    Realed rl = new;
    Braced br = new;
    repeat (256) begin
      void'(sz.randomize());
      case (sz.mode)
        little: begin littles++; if (sz.len < 10) selected++; end
        big: begin bigs++; if (sz.len > 100) selected++; end
        default: begin others++; if (sz.len >= 0 && sz.len <= 200) selected++; end
      endcase
    end
    $display("mode selects len below 10, above 100 or unconstrained: %0d of 256, every mode drawn: %0d",
             selected, littles > 0 && bigs > 0 && others > 0);
    repeat (64) begin
      void'(fx.randomize());
      if (fx.mode == other && fx.len == 50) left_other++;
    end
    $display("len held to 50 leaves mode other: %0d of 64", left_other);
    repeat (256) begin
      void'(ns.randomize());
      case (ns.mode)
        little: begin n_littles++; if (ns.len < 10) nested++; end
        big: begin n_bigs++; if (ns.len <= 100) n_bigs_low++; if (ns.len >= 0 && ns.len <= 200) nested++; end
        default: begin n_others++; if (ns.len > 100) nested++; end
      endcase
    end
    $display("the else goes with the inner if: %0d of 256, every mode drawn: %0d, big draws len at or below 100: %0d",
             nested, n_littles > 0 && n_bigs > 0 && n_others > 0, n_bigs_low > 0);
    repeat (64) begin
      void'(rl.randomize());
      if (rl.r == 0.5) halves++;
      if ((rl.r > 1.0 && rl.k == 2) || (rl.r < 1.0 && rl.k == 3)) realed++;
    end
    $display("a real expression selects k: %0d of 64, both reals drawn: %0d",
             realed, halves > 0 && halves < 64);
    repeat (128) begin
      void'(br.randomize());
      if (br.x > 7) begin
        highs++;
        if (br.y > 7 && br.y < 12) braced++;
      end else begin
        if (br.y < 4) braced++;
      end
    end
    $display("an unnamed set holds whole above 7 and a relation below: %0d of 128, some x above 7: %0d",
             braced, highs > 0 && highs < 128);
    $finish;
  end
endmodule
