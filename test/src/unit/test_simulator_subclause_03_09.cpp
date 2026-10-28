// §3.9 (printed page 53) gives every module, interface, program and checker a
// name space of its own: a name one of these building blocks declares belongs
// to that block alone, so another block declaring the same name neither
// collides with it nor reaches it. Each case below declares one name in a
// child block and in the module instantiating it, with different values or
// widths, and reads the child's own declaration back after the run; nothing is
// reported.

#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// A program's `x` is its own: the program's initial reads 5 from its own
// declaration, and the instantiating module's `x` keeps 9.
TEST(BuildingBlockNameSpace, AProgramsVariableIsItsOwnBesideItsModules) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "program p;\n"
      "  int x = 5;\n"
      "  int y;\n"
      "  initial y = x;\n"
      "endprogram\n"
      "module top;\n"
      "  int x = 9;\n"
      "  p u();\n"
      "endmodule\n",
      f, "u.y");
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 5u);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 9u);
}

// A checker's `x` is its own: the checker variable `y` is initialized from the
// checker's `x`, 5, and the instantiating module's `x` keeps 9.
TEST(BuildingBlockNameSpace, ACheckersVariableIsItsOwnBesideItsModules) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "checker chk(logic clk);\n"
      "  int x = 5;\n"
      "  int y = x;\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk;\n"
      "  int x = 9;\n"
      "  chk c(clk);\n"
      "endmodule\n",
      f, "c.y");
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 5u);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 9u);
}

// A child's typedef `t` is its own: the child's `a` takes the child's 4-bit
// `t`, the top's `b` its own 8-bit `t`, whichever module is elaborated first.
TEST(BuildingBlockNameSpace, AChildsTypedefIsItsOwnBesideItsModules) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module child;\n"
      "  typedef logic [3:0] t;\n"
      "  t a;\n"
      "endmodule\n"
      "module top;\n"
      "  typedef logic [7:0] t;\n"
      "  t b;\n"
      "  child c();\n"
      "endmodule\n",
      f, "c.a");
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.width, 4u);
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.width, 8u);
}

// A child's bare call of `f` runs the child's own function, returning 1, not
// the instantiating module's `f` of the same name, returning 2.
TEST(BuildingBlockNameSpace, AChildsCallRunsItsOwnFunctionBesideItsModules) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module child;\n"
      "  function int f();\n"
      "    return 1;\n"
      "  endfunction\n"
      "  int y;\n"
      "  initial y = f();\n"
      "endmodule\n"
      "module top;\n"
      "  function int f();\n"
      "    return 2;\n"
      "  endfunction\n"
      "  child c();\n"
      "endmodule\n",
      f, "c.y");
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 1u);
}

}  // namespace
