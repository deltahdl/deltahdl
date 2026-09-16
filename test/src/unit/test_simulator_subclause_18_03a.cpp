#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// These tests drive the 18.3 "important properties of constraints" end to end.
// Each program elaborates a real class, calls randomize() on an object of it,
// and copies the outcome into module variables the harness reads, so the
// behavior observed is that of parse/elaborate/run applying the rule through
// the production randomize() path (eval_randomize.cpp + the constraint solver)
// rather than a hand-built solver state. 18.4 supplies the rand data-member
// declarations the rules operate on and 18.6.1 supplies randomize() itself.

// 18.3: for an active random variable of enum type, the solver shall select a
// value only from the set of named constants of that enum. The named set here
// is {1, 4, 9}, leaving 0, 2, 3, 5..8, 10..15 as castable-but-unnamed values in
// the 4-bit declared range. Over many draws every value read back is one of the
// three named constants -- an unrestricted 4-bit draw would land outside the
// set on most iterations, so an all-in-set result demonstrates the enum-domain
// restriction is applied through the real randomize() path (the type is a named
// typedef declared on the class, matching the 18.3 MyBus atype form).
TEST(EnumRandomVariable, SelectsOnlyNamedConstants) {
  const char* src =
      "class Pkt;\n"
      "  typedef enum bit [3:0] { LO = 1, MID = 4, HI = 9 } lvl_e;\n"
      "  rand lvl_e x;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int v;\n"
      "  int all_in_set;\n"
      "  initial begin\n"
      "    Pkt p = new;\n"
      "    all_in_set = 1;\n"
      "    for (int i = 0; i < 40; i++) begin\n"
      "      ok = p.randomize();\n"
      "      v = p.x;\n"
      // A single condition covers both the accepting side (a solved value is
      // one of the named constants) and the rejecting side (the solver never
      // assigns an outside-the-set value such as 0, 2, or 3).
      "      if (!(v == 1 || v == 4 || v == 9)) all_in_set = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "all_in_set"), 1u);
}

// 18.3: the named-constant restriction covers every active random variable of
// enum type, including a cyclic randc one. randc (18.4.2) only fixes the order
// in which values are visited without repeating; it does not widen the domain,
// so every value a randc enum variable takes is still one of the enum's named
// constants. Built from real randc source syntax and driven through randomize()
// so the observation is of the production solver's randc enum path.
TEST(EnumRandomVariable, RandcEnumSelectsOnlyNamedConstants) {
  const char* src =
      "class Pkt;\n"
      "  typedef enum bit [3:0] { LO = 1, MID = 4, HI = 9 } lvl_e;\n"
      "  randc lvl_e x;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int v;\n"
      "  int all_in_set;\n"
      "  initial begin\n"
      "    Pkt p = new;\n"
      "    all_in_set = 1;\n"
      "    for (int i = 0; i < 40; i++) begin\n"
      "      ok = p.randomize();\n"
      "      v = p.x;\n"
      "      if (!(v == 1 || v == 4 || v == 9)) all_in_set = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "all_in_set"), 1u);
}

// 18.3: the set of random values chosen shall satisfy all of the constraints. A
// single named constraint block bounds x to [400, 410]; every solved value read
// back over many draws lands inside that range.
TEST(ConstraintProperties, ChosenValuesSatisfyConstraints) {
  const char* src =
      "class C;\n"
      "  rand bit [15:0] x;\n"
      "  constraint c { x >= 400; x <= 410; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int v;\n"
      "  int all_ok;\n"
      "  initial begin\n"
      "    C obj = new;\n"
      "    all_ok = 1;\n"
      "    for (int i = 0; i < 20; i++) begin\n"
      "      ok = obj.randomize();\n"
      "      v = obj.x;\n"
      "      if (!(v >= 400 && v <= 410)) all_ok = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "all_ok"), 1u);
}

// 18.3: the constraint solver shall find a solution whenever one exists, and
// can fail only when the problem is over-constrained. Two contradictory
// equalities (x == 5 and x == 6) leave no satisfying value, so randomize()
// reports failure (returns 0) rather than producing an out-of-constraint value.
TEST(ConstraintProperties, OverConstrainedProblemFails) {
  const char* src =
      "class C;\n"
      "  rand bit [7:0] x;\n"
      "  constraint contradiction { x == 5; x == 6; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    C obj = new;\n"
      "    ok = obj.randomize();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
}

// 18.3: an unconstrained random variable is assigned any value in its declared
// range. x has no constraint, so successive randomize() draws are unrestricted
// yet always stay within the 4-bit declared range 0..15.
TEST(ConstraintProperties, UnconstrainedVariableStaysInDeclaredRange) {
  const char* src =
      "class C;\n"
      "  rand bit [3:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int v;\n"
      "  int all_in_range;\n"
      "  initial begin\n"
      "    C obj = new;\n"
      "    all_in_range = 1;\n"
      "    for (int i = 0; i < 40; i++) begin\n"
      "      ok = obj.randomize();\n"
      "      v = obj.x;\n"
      "      if (!(v >= 0 && v <= 15)) all_in_range = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "all_in_range"), 1u);
}

}  // namespace
