// §18.5.5 Implication: the operator -> declares an expression that implies
// a constraint, the expression any integral or real expression and the
// consequent any constraint or an unnamed constraint set. a -> b is the
// Boolean (!a || b): where the expression is true every constraint of the
// set holds, otherwise the values are unconstrained, and conversely where
// the set cannot hold the expression is false. Both sides are
// interdependent, so len constrains mode as mode constrains len. The
// Sized here is the clause's example, mode implying len below 10 when
// little and above 100 when big; the Fixed holds len to 50, which leaves
// mode neither little nor big; the Pair is the clause's 4-bit a and b
// under (a == 0) -> (b == 1), which leaves 241 of the 256 combinations and
// a == 0 a probability of 1/241; the Guarded implies k from a real r; and
// the Braced implies an unnamed set of two relations.
typedef enum {little, big, other} mode_t;

class Sized;
  rand mode_t mode;
  rand int len;
  constraint range { len >= 0; len <= 200; }
  constraint by_mode {
    (mode == little) -> len < 10;
    (mode == big) -> len > 100;
  }
endclass

class Fixed;
  rand mode_t mode;
  rand int len;
  constraint mid { len == 50; }
  constraint by_mode {
    (mode == little) -> len < 10;
    (mode == big) -> len > 100;
  }
endclass

class Pair;
  rand bit [3:0] a;
  rand bit [3:0] b;
  constraint c { (a == 0) -> (b == 1); }
endclass

class Guarded;
  rand real r;
  rand int k;
  constraint pick { r dist { 0.5 := 1, 1.5 := 1 }; }
  constraint by_r {
    (r > 1.0) -> k == 2;
    (r < 1.0) -> k == 3;
  }
endclass

class Braced;
  rand bit [3:0] x;
  rand bit [3:0] y;
  constraint c { (x > 7) -> { y > 7; y < 12; } }
endclass

module implication_constraints;
  int implied = 0, littles = 0, bigs = 0, others = 0;
  int left_other = 0, consistent = 0, zeros = 0, guarded = 0, halves = 0;
  int braced = 0, highs = 0;
  initial begin
    Sized sz = new;
    Fixed fx = new;
    Pair pr = new;
    Guarded gd = new;
    Braced br = new;
    repeat (256) begin
      void'(sz.randomize());
      case (sz.mode)
        little: begin littles++; if (sz.len < 10) implied++; end
        big: begin bigs++; if (sz.len > 100) implied++; end
        default: begin others++; if (sz.len >= 0 && sz.len <= 200) implied++; end
      endcase
    end
    $display("mode implies len below 10, above 100 or unconstrained: %0d of 256, every mode drawn: %0d",
             implied, littles > 0 && bigs > 0 && others > 0);
    repeat (64) begin
      void'(fx.randomize());
      if (fx.mode == other && fx.len == 50) left_other++;
    end
    $display("len held to 50 leaves mode other: %0d of 64", left_other);
    repeat (4820) begin
      void'(pr.randomize());
      if (pr.a != 0 || pr.b == 1) consistent++;
      if (pr.a == 0) zeros++;
    end
    $display("a == 0 implies b == 1: %0d of 4820, a == 0 about a 241st of the time: %0d",
             consistent, zeros > 0 && zeros < 100);
    repeat (64) begin
      void'(gd.randomize());
      if (gd.r == 0.5) halves++;
      if ((gd.r > 1.0 && gd.k == 2) || (gd.r < 1.0 && gd.k == 3)) guarded++;
    end
    $display("a real expression implies k: %0d of 64, both reals drawn: %0d",
             guarded, halves > 0 && halves < 64);
    repeat (128) begin
      void'(br.randomize());
      if (br.x > 7) begin
        highs++;
        if (br.y > 7 && br.y < 12) braced++;
      end
    end
    $display("an unnamed set holds whole wherever x is above 7: %0d, some x above 7: %0d",
             braced == highs, highs > 0);
    $finish;
  end
endmodule
