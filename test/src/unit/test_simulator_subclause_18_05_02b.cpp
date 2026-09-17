#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// The classes of test/src/e2e/constraint_inheritance.sv around the
// statements of an initial that holds a Base b, a Derived d, a Fixed f, a
// Range r, a Sealed s and a Base handle h, with the module's counters.
std::string Design(const std::string& body) {
  return "class Base;\n"
         "  rand int x;\n"
         "  constraint lo { x >= 0; }\n"
         "  constraint hi { x < 100; }\n"
         "endclass\n"
         "class Derived extends Base;\n"
         "  constraint :extends hi { x < 10; }\n"
         "  constraint even { x % 2 == 0; }\n"
         "endclass\n"
         "class Fixed extends Base;\n"
         "  constraint hi;\n"
         "endclass\n"
         "constraint Fixed::hi { x == 42; }\n"
         "virtual class Bounded;\n"
         "  rand int v;\n"
         "  pure constraint within;\n"
         "endclass\n"
         "class Range extends Bounded;\n"
         "  constraint within { v inside {[1:3]}; }\n"
         "endclass\n"
         "class Sealed;\n"
         "  rand int w;\n"
         "  constraint :initial :final own { w inside {7, 9}; }\n"
         "endclass\n"
         "module t;\n"
         "  int base_wide = 0, base_over = 0, derived_narrow = 0, fixed_42 = "
         "0;\n"
         "  int through_base = 0, range_ok = 0, sealed_ok = 0;\n"
         "  initial begin\n"
         "    Base b = new;\n"
         "    Derived d = new;\n"
         "    Fixed f = new;\n"
         "    Range r = new;\n"
         "    Sealed s = new;\n"
         "    Base h;\n" +
         body +
         "  end\n"
         "endmodule\n";
}

// 18.5.2: a derived constraint of an inherited name replaces the inherited
// one and one of a new name adds to the rest, while the base's own blocks
// still hold for the base.
TEST(ConstraintInheritanceRun,
     ADerivedBlockReplacesItsNamesakeAndAddsToTheRest) {
  const std::string kSrc = Design(
      "    repeat (32) begin\n"
      "      void'(b.randomize());\n"
      "      if (b.x >= 0 && b.x < 100) base_wide++;\n"
      "      if (b.x >= 10) base_over++;\n"
      "    end\n"
      "    repeat (32) begin\n"
      "      void'(d.randomize());\n"
      "      if (d.x >= 0 && d.x < 10 && d.x % 2 == 0) derived_narrow++;\n"
      "    end\n"
      "    $display(\"%0d %0d %0d\", base_wide, base_over > 0, "
      "derived_narrow);\n"
      "    $finish;\n");
  SimFixture f;
  EXPECT_EQ(RunCapture(kSrc, f), "32 1 32\n$finish at time 0\n");
}

// 18.5.2: randomize() is virtual, so through a Base handle it honors the
// Derived object's constraints.
TEST(ConstraintInheritanceRun, RandomizeThroughABaseHandleHonorsTheObjects) {
  const std::string kSrc = Design(
      "    h = d;\n"
      "    repeat (32) begin\n"
      "      void'(h.randomize());\n"
      "      if (h.x >= 0 && h.x < 10 && h.x % 2 == 0) through_base++;\n"
      "    end\n"
      "    $finish;\n");
  EXPECT_EQ(RunAndGet(kSrc, "through_base"), uint64_t{32});
}

// 18.5.2: a derived prototype of an inherited name replaces the inherited
// constraint, completed as 18.5.1 has it.
TEST(ConstraintInheritanceRun, ADerivedPrototypeReplacesTheInheritedBlock) {
  const std::string kSrc = Design(
      "    repeat (32) begin\n"
      "      void'(f.randomize());\n"
      "      if (f.x == 42) fixed_42++;\n"
      "    end\n"
      "    $finish;\n");
  EXPECT_EQ(RunAndGet(kSrc, "fixed_42"), uint64_t{32});
}

// 18.5.2: the non-abstract class's constraint of a pure constraint's name
// implements it and holds; a block with :initial :final holds as any does.
TEST(ConstraintInheritanceRun,
     APureConstraintsImplementationAndASealedBlockHold) {
  const std::string kSrc = Design(
      "    repeat (32) begin\n"
      "      void'(r.randomize());\n"
      "      if (r.v >= 1 && r.v <= 3) range_ok++;\n"
      "    end\n"
      "    repeat (32) begin\n"
      "      void'(s.randomize());\n"
      "      if (s.w == 7 || s.w == 9) sealed_ok++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", range_ok, sealed_ok);\n"
      "    $finish;\n");
  SimFixture f;
  EXPECT_EQ(RunCapture(kSrc, f), "32 32\n$finish at time 0\n");
}

}  // namespace
