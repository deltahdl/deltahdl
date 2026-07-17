#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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

// §11.3.3 SHALL #3 for the sized, unsigned-based literal form (the third
// enumerated form): a sized unsigned base specifier is unsigned just like the
// unsized 'd form, so -32'd12 negates and divides as an unsigned 32-bit value
// and produces 1431655761 at run time -- identical to the unsized -'d12 / 3
// case above, showing the size annotation does not change the sign rule.
TEST(IntegerLiteralSim, NegatedSizedUnsignedBasedDivThree) {
  auto result = RunAndGet(
      "module t;\n"
      "  integer x;\n"
      "  initial x = -32'd12 / 3;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result & 0xFFFFFFFFu, 1431655761u);
}

// §11.3.3 applies wherever an integer literal is an operand, not only in a
// procedural assignment. Here the unsigned-based literal drives the same
// unsigned negation/division through a declaration initializer instead of an
// initial-block assignment, so the sign rule is observed in that syntactic
// position too. The initializer is evaluated as the variable comes into being.
TEST(IntegerLiteralSim, UnsignedBasedLiteralInDeclInitIsUnsigned) {
  auto result = RunAndGet(
      "module t;\n"
      "  integer x = -'d12 / 3;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result & 0xFFFFFFFFu, 1431655761u);
}

// SHALL #2 in the same declaration-initializer position: an unbased literal is
// signed, so -12 / 3 in a decl initializer resolves to -4 (0xFFFFFFFC), the
// signed counterpart of the unsigned-based case above. The pair makes the
// SHALL #1 "differs from a based literal" contrast observable within the
// declaration-initializer code path, not only in a procedural assignment.
TEST(IntegerLiteralSim, UnbasedLiteralInDeclInitIsSigned) {
  auto result = RunAndGet(
      "module t;\n"
      "  integer x = -12 / 3;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result & 0xFFFFFFFFu, 0xFFFFFFFCu);
}

}  // namespace
