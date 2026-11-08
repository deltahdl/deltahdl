#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(IntegerLiteralSim, LiteralAssignedThroughParameter) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  parameter int P = 42;\n"
      "  logic [7:0] x;\n"
      "  initial x = P;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(IntegerLiteralSim, NegatedUnsignedSizedLiteral) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = -8'd6;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 250u);
}

TEST(IntegerLiteralSim, NegatedUnbasedLiteralIsTwosComplement) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = -1;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 255u);
}

TEST(IntegerLiteralSim, NegatedUnbasedDivThree) {
  auto result = RunAndGet(
      "module t;\n"
      "  integer x;\n"
      "  initial x = -12 / 3;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result & 0xFFFFFFFFu, 0xFFFFFFFCu);
}

TEST(IntegerLiteralSim, NegatedUnsignedBasedDivThree) {
  auto result = RunAndGet(
      "module t;\n"
      "  integer x;\n"
      "  initial x = -'d12 / 3;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result & 0xFFFFFFFFu, 1431655761u);
}

TEST(IntegerLiteralSim, NegatedSignedBasedDivThree) {
  auto result = RunAndGet(
      "module t;\n"
      "  integer x;\n"
      "  initial x = -'sd12 / 3;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result & 0xFFFFFFFFu, 0xFFFFFFFCu);
}

TEST(IntegerLiteralSim, NegatedSizedSignedBasedDivThree) {
  auto result = RunAndGet(
      "module t;\n"
      "  integer x;\n"
      "  initial x = -4'sd12 / 3;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result & 0xFFFFFFFFu, 1u);
}

TEST(IntegerLiteralSim, NegatedSizedUnsignedBasedDivThree) {
  auto result = RunAndGet(
      "module t;\n"
      "  integer x;\n"
      "  initial x = -32'd12 / 3;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result & 0xFFFFFFFFu, 1431655761u);
}

TEST(IntegerLiteralSim, UnsignedBasedLiteralInDeclInitIsUnsigned) {
  auto result = RunAndGet(
      "module t;\n"
      "  integer x = -'d12 / 3;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result & 0xFFFFFFFFu, 1431655761u);
}

TEST(IntegerLiteralSim, UnbasedLiteralInDeclInitIsSigned) {
  auto result = RunAndGet(
      "module t;\n"
      "  integer x = -12 / 3;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result & 0xFFFFFFFFu, 0xFFFFFFFCu);
}

}  // namespace
