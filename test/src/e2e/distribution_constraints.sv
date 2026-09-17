// §18.5.3 Distribution: beside the set membership operator, a constraint
// may weight the members of a set, a distribution being both a relational
// test for membership and a statistical distribution over its members.
// Each item of the set is a value or a range with a weight, := or :/, an
// unweighted integral item weighing 1; absent other constraints, the
// probability of an item is proportional to its weight, and a nonzero
// weight never removes a value from the solution space, while a value the
// distribution names only with a total weight of zero is excluded. The two
// operators differ on a range: := weighs each element, the range's weight
// being its size times the weight, counting elements other constraints
// exclude, while :/ weighs the range as a whole; either way the weight
// applies to the range as a whole, so with 100 and 101 excluded the range
// [100:102] weighted 3 still leaves 102 three times as likely as 103. A
// value in several items adds their weights, a zero weight included, and
// a default item weighs every value of the type no other item names. A
// distribution may mix real and integral values, a range of reals using
// :/ with a weight and a tolerance range [centre +%- percent] naming the
// reals within that percentage of the centre. The classes here draw each
// case in turn and the counts are compared against the clause's ratios.
class Weighted;
  rand int x;
  constraint c { x dist {100 := 1, 200 := 2, 300 := 5}; }
endclass

class Divided;
  rand int x;
  constraint c { x dist {100 :/ 1, 200 :/ 2, 300 :/ 5}; }
endclass

class Excluded;
  rand int x;
  constraint c { x != 200; x dist {100 := 1, 200 := 2, 300 := 5}; }
endclass

class PerElement;
  rand int x;
  constraint c { x dist {[100:102] := 1, 103 := 1}; }
endclass

class Whole;
  rand int x;
  constraint c { x dist {[100:102] :/ 1, 103 := 1}; }
endclass

class Narrowed;
  rand int x;
  constraint c { x > 101; x dist {[100:102] := 1, 103 := 1}; }
endclass

class Additive;
  rand int x;
  constraint c { x dist {[100:102] := 1, 101 := 1}; }
endclass

class ZeroAdded;
  rand int x;
  constraint c { x dist {100 :/ 0, [100:102] :/ 1}; }
endclass

class ZeroAlone;
  rand int x;
  constraint c { x dist {17 := 0, 42 := 1}; }
endclass

class Defaulted;
  rand int x;
  constraint c { x dist {[100:102] :/ 3, default :/ 1}; }
endclass

class Mixed;
  rand real a;
  constraint c {
    a dist { -100 := 5, [0.70:1.43] :/ 1, [3.30 +%- 1.0] :/ 13,
             [1.43:3.65] :/ 1 };
  }
endclass

module distribution_constraints;
  int n100, n101, n102, n103, n200, n300, other;

  task automatic reset();
    n100 = 0; n101 = 0; n102 = 0; n103 = 0; n200 = 0; n300 = 0; other = 0;
  endtask

  task automatic count(int x);
    case (x)
      100: n100++;
      101: n101++;
      102: n102++;
      103: n103++;
      200: n200++;
      300: n300++;
      default: other++;
    endcase
  endtask

  initial begin
    Weighted w = new;
    Divided d = new;
    Excluded e = new;
    PerElement pe = new;
    Whole wh = new;
    Narrowed nr = new;
    Additive ad = new;
    ZeroAdded za = new;
    ZeroAlone zo = new;
    Defaulted df = new;
    Mixed m = new;
    int stated, near, rest;

    reset();
    repeat (256) begin void'(w.randomize()); count(w.x); end
    $display("a := set draws only its members, 300 the most and 100 the least: %0d %0d",
             other == 0 && n100 > 0 && n200 > 0 && n300 > 0,
             n300 > n200 && n200 > n100);

    reset();
    repeat (256) begin void'(d.randomize()); count(d.x); end
    $display(":/ weighs single values as := does: %0d %0d",
             other == 0 && n100 > 0 && n200 > 0 && n300 > 0,
             n300 > n200 && n200 > n100);

    reset();
    repeat (256) begin void'(e.randomize()); count(e.x); end
    $display("x != 200 leaves 100 and 300 at 1:5: %0d %0d",
             other == 0 && n200 == 0 && n100 > 0 && n300 > 0, n300 > 2 * n100);

    reset();
    repeat (400) begin void'(pe.randomize()); count(pe.x); end
    stated = n100 + n101 + n102;
    $display(":= weighs each element, [100:102] to 103 at 3:1: %0d %0d",
             other == 0 && n103 > 0, stated > 2 * n103);

    reset();
    repeat (400) begin void'(wh.randomize()); count(wh.x); end
    stated = n100 + n101 + n102;
    $display(":/ weighs the range whole, [100:102] to 103 at 1:1: %0d %0d",
             other == 0 && n103 > 0, stated < 2 * n103 && n103 < 2 * stated);

    reset();
    repeat (400) begin void'(nr.randomize()); count(nr.x); end
    $display("x > 101 leaves the range its whole weight, 102 to 103 at 3:1: %0d %0d",
             other == 0 && n100 == 0 && n101 == 0 && n102 > 0 && n103 > 0,
             n102 > 2 * n103);

    reset();
    repeat (400) begin void'(ad.randomize()); count(ad.x); end
    $display("a value in two items adds their weights, 101 at 1:2:1: %0d %0d",
             other == 0 && n103 == 0 && n100 > 0 && n102 > 0,
             n101 > n100 && n101 > n102);

    reset();
    repeat (128) begin void'(za.randomize()); count(za.x); end
    $display("a zero weight adds to a nonzero item's, 100 staying reachable: %0d %0d",
             other == 0 && n103 == 0, n100 > 0);

    reset();
    repeat (32) begin void'(zo.randomize()); if (zo.x == 42) n100++; else other++; end
    $display("a value weighted zero in every item is excluded: %0d", n100 == 32 && other == 0);

    reset();
    repeat (400) begin void'(df.randomize()); count(df.x); end
    stated = n100 + n101 + n102;
    rest = n103 + other;
    $display("default weighs the rest of the domain, [100:102] to it at 3:1: %0d %0d",
             stated > 0 && rest > 0, stated > 2 * rest);

    reset(); stated = 0; near = 0; rest = 0;
    repeat (200) begin
      void'(m.randomize());
      if (m.a == -100.0) stated++;
      else if (m.a >= 3.267 && m.a <= 3.333) near++;
      else if (m.a >= 0.70 && m.a <= 3.65) rest++;
      else other++;
    end
    $display("a real dist mixes -100 with real ranges, 3.3 within 1 percent at 13 of 20: %0d %0d",
             other == 0 && stated > 0 && rest > 0, near > stated + rest);
    $finish;
  end
endmodule
