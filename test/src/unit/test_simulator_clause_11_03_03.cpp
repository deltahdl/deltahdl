#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// --- Literal used as expression operand ---

TEST(IntegerLiteralSim, LiteralAssignedThroughParameter) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter int P = 42;\n"
      "  logic [7:0] x;\n"
      "  initial x = P;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// --- Negation of unsigned literal ---

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

// --- Negation/division examples from §11.3.3 ---

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

}  // namespace
