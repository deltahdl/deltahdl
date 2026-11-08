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
  pure constraint bounds;
endclass

class Range extends Bounded;
  constraint bounds { v inside {[1:3]}; }
endclass

class Sealed;
  rand int w;
  constraint :initial :final own { w inside {7, 9}; }
endclass

module constraint_inheritance;
  int base_wide = 0, base_over = 0, derived_narrow = 0, fixed_42 = 0;
  int through_base = 0, range_ok = 0, sealed_ok = 0;
  initial begin
    static Base b = new;
    static Derived d = new;
    static Fixed f = new;
    static Range r = new;
    static Sealed s = new;
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
