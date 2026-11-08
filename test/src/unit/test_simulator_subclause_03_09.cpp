#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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
