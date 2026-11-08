#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(EmptyStringLiteralSim, EmptyStringLiteralIsZero) {
  SimFixture f;
  auto* expr = ParseExprFrom("\"\"", f);
  ASSERT_NE(expr, nullptr);
  auto val = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(val.ToUint64(), 0u);
  EXPECT_EQ(val.width, 8u);
}

TEST(EmptyStringLiteralSim, EmptyStringEqualsNul) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic result;\n"
      "  initial result = (\"\" == 8'd0);\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(EmptyStringLiteralSim, EmptyStringDiffersFromStringZero) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic result;\n"
      "  initial result = (\"\" == \"0\");\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(EmptyStringLiteralSim, StringZeroHasAsciiValue) {
  SimFixture f;
  auto* expr = ParseExprFrom("\"0\"", f);
  ASSERT_NE(expr, nullptr);
  auto val = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(val.ToUint64(), 0x30u);
}

TEST(EmptyStringLiteralSim, EmptyStringEqualsExplicitNulEscape) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic result;\n"
      "  initial result = (\"\" == \"\\0\");\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(EmptyStringLiteralSim, ExplicitNulEscapeIsZero) {
  SimFixture f;
  auto* expr = ParseExprFrom("\"\\0\"", f);
  ASSERT_NE(expr, nullptr);
  auto val = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(val.ToUint64(), 0u);
  EXPECT_EQ(val.width, 8u);
}

TEST(EmptyStringLiteralSim, EmptyStringAssignedToVector) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [7:0] v;\n"
      "  initial v = \"\";\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(EmptyStringLiteralSim, EmptyStringIsFalsyInConditional) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    result = 1;\n"
      "    if (\"\") result = 0;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(EmptyStringLiteralSim, EmptyStringOccupiesNulByteInConcatenation) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [8*3:1] v;\n"
      "  initial v = {\"A\", \"\", \"B\"};\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x410042u);
}

}  // namespace
