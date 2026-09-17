// §18.5.2 Constraint inheritance: constraints are inherited as other class
// members are, a derived class inheriting every constraint of its
// superclass; a derived constraint of an inherited name replaces the
// inherited one and a derived constraint of a new name is an additional
// constraint; randomize() is virtual, so it honors the constraints of the
// object it is called on whatever the type of the handle; a derived
// prototype of an inherited name replaces the inherited constraint and is
// completed as an external block; an abstract class may declare a pure
// constraint, an obligation on every non-abstract derived class to
// provide a constraint of that name; and the :initial, :extends and :final
// specifiers state that a constraint is not an override, is one, and may
// not be replaced further. The Base here holds x at least 0 and below 100
// in two blocks; a Derived replaces hi to hold x below 10, marked
// :extends, and adds even; a Fixed replaces hi through a prototype
// completed outside the class to hold x to 42; a Range implements the pure
// constraint of the abstract Bounded; and a Sealed declares its own
// :initial :final block.
class Base;
  rand int x;
  constraint lo { x >= 0; }
  constraint hi { x < 100; }
endclass

class Derived extends Base;
  constraint :extends hi { x < 10; }
  constraint even { x % 2 == 0; }
endclass

class Fixed extends Base;
  constraint hi;
endclass

constraint Fixed::hi { x == 42; }

virtual class Bounded;
  rand int v;
  pure constraint within;
endclass

class Range extends Bounded;
  constraint within { v inside {[1:3]}; }
endclass

class Sealed;
  rand int w;
  constraint :initial :final own { w inside {7, 9}; }
endclass

module constraint_inheritance;
  int base_wide = 0, base_over = 0, derived_narrow = 0, fixed_42 = 0;
  int through_base = 0, range_ok = 0, sealed_ok = 0;
  initial begin
    Base b = new;
    Derived d = new;
    Fixed f = new;
    Range r = new;
    Sealed s = new;
    Base h;
    repeat (32) begin
      void'(b.randomize());
      if (b.x >= 0 && b.x < 100) base_wide++;
      if (b.x >= 10) base_over++;
    end
    $display("the base's own blocks hold: %0d of 32 in 0 to 99, some at least 10: %0d",
             base_wide, base_over > 0);
    repeat (32) begin
      void'(d.randomize());
      if (d.x >= 0 && d.x < 10 && d.x % 2 == 0) derived_narrow++;
    end
    $display("the derived's hi replaces the inherited one and even adds to lo: %0d of 32",
             derived_narrow);
    h = d;
    repeat (32) begin
      void'(h.randomize());
      if (h.x >= 0 && h.x < 10 && h.x % 2 == 0) through_base++;
    end
    $display("randomize() through a Base handle honors the Derived's constraints: %0d of 32",
             through_base);
    repeat (32) begin
      void'(f.randomize());
      if (f.x == 42) fixed_42++;
    end
    $display("a derived prototype completed outside the class replaces hi: %0d of 32",
             fixed_42);
    repeat (32) begin
      void'(r.randomize());
      if (r.v >= 1 && r.v <= 3) range_ok++;
    end
    $display("the implementation of a pure constraint holds: %0d of 32", range_ok);
    repeat (32) begin
      void'(s.randomize());
      if (s.w == 7 || s.w == 9) sealed_ok++;
    end
    $display("an :initial :final block holds as any block does: %0d of 32", sealed_ok);
    $finish;
  end
endmodule
