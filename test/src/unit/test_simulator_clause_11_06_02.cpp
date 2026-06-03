#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

// §11.6.2 illustrates the expression bit-length problem: during evaluation an
// interim result takes the size of the largest operand, and in an assignment
// the left-hand side is one of those operands. These tests observe the
// simulator applying that rule on the subclause's own examples.
namespace {

// The interim (a + b) is self-determined to 16 bits — the width of the largest
// operand, no wider than the 16-bit destination — so the carry out of the add
// is lost before the right shift, exactly the problem the subclause describes.
TEST(ExpressionBitLengthProblem, InterimAddSizedToOperandsLosesCarry) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] a, b, answer;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    answer = (a + b) >> 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("answer");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x0000u);
}

// Adding an integer-sized 0 brings a wider operand into the expression, so the
// interim sum is evaluated with enough bits to keep the carry and the shift
// produces the intended result.
TEST(ExpressionBitLengthProblem, WideningInterimWithIntegerPreservesCarry) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] a, b, answer;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    answer = (a + b + 0) >> 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("answer");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x8000u);
}

// The other half of the rule: in an assignment the left-hand side counts as one
// of the operands that size the interim result. Here the destination is one bit
// wider than both addends, so the add is evaluated with that extra bit and the
// carry survives — the affirmative counterpart to the equal-width case above.
TEST(ExpressionBitLengthProblem, AssignmentLhsWidthSizesInterimPreservesCarry) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] a, b;\n"
      "  logic [16:0] answer;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    answer = a + b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("answer");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x10000u);
}

// In `c ? (a & b) : d`, a & b is self-determined to 4 bits, but the conditional
// expression sizes its operands to the largest of the two branches. Because d
// is 5 bits wide, the selected a & b result is widened to 5 bits — answer 01000
// in the subclause's example.
TEST(ExpressionBitLengthProblem, ConditionalContextWidensNarrowBranch) {
  SimFixture f;
  MakeVar(f, "a", 4, 9);
  MakeVar(f, "b", 4, 8);
  MakeVar(f, "c", 1, 1);
  MakeVar(f, "d", 5, 0);

  auto* tern = f.arena.Create<Expr>();
  tern->kind = ExprKind::kTernary;
  tern->condition = MakeId(f.arena, "c");
  tern->true_expr =
      MakeBinary(f.arena, TokenKind::kAmp, MakeId(f.arena, "a"),
                 MakeId(f.arena, "b"));
  tern->false_expr = MakeId(f.arena, "d");

  auto result = EvalExpr(tern, f.ctx, f.arena);

  EXPECT_EQ(result.width, 5u);
  EXPECT_EQ(result.ToUint64(), 8u);
}

}
