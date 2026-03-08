#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §11.6: ContextWidth returns max of self-determined and context.
TEST(Elaboration, ContextWidthMaxOfSelfAndContext) {
  TypedefMap typedefs;
  Expr a;
  a.kind = ExprKind::kIntegerLiteral;
  a.int_val = 0;
  // Self-determined width of integer literal is 32.
  EXPECT_EQ(InferExprWidth(&a, typedefs), 32u);
  // Context width < self: returns self.
  EXPECT_EQ(ContextWidth(&a, 16, typedefs), 32u);
  // Context width > self: returns context.
  EXPECT_EQ(ContextWidth(&a, 64, typedefs), 64u);
  // Context width == self: returns either.
  EXPECT_EQ(ContextWidth(&a, 32, typedefs), 32u);
}

// §11.6: Binary addition self-determined width is max of operand widths.
TEST(Elaboration, ExprBitLengthBinaryAddition) {
  TypedefMap typedefs;
  Expr lhs;
  lhs.kind = ExprKind::kIntegerLiteral;
  lhs.int_val = 0;
  Expr rhs;
  rhs.kind = ExprKind::kIntegerLiteral;
  rhs.int_val = 0;
  Expr add;
  add.kind = ExprKind::kBinary;
  add.op = TokenKind::kPlus;
  add.lhs = &lhs;
  add.rhs = &rhs;
  // Both operands are 32-bit integer literals → max = 32.
  EXPECT_EQ(InferExprWidth(&add, typedefs), 32u);
}

// §11.6: Elaboration succeeds for assignment with wider LHS.
TEST(Elaboration, AssignmentWiderLhsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] a, b;\n"
      "  logic [16:0] result;\n"
      "  initial result = a + b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §11.6: Elaboration succeeds for narrower LHS (truncation).
TEST(Elaboration, AssignmentNarrowerLhsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] a, b;\n"
      "  logic [7:0] result;\n"
      "  initial result = a + b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §11.6: Ternary expression width is max of true/false branch widths.
TEST(Elaboration, TernaryExprBitLength) {
  TypedefMap typedefs;
  Expr cond;
  cond.kind = ExprKind::kIntegerLiteral;
  cond.int_val = 1;
  Expr true_e;
  true_e.kind = ExprKind::kIntegerLiteral;
  true_e.int_val = 0;
  Expr false_e;
  false_e.kind = ExprKind::kIntegerLiteral;
  false_e.int_val = 0;
  Expr tern;
  tern.kind = ExprKind::kTernary;
  tern.condition = &cond;
  tern.true_expr = &true_e;
  tern.false_expr = &false_e;
  // Both branches are 32-bit integer literals → max = 32.
  EXPECT_EQ(InferExprWidth(&tern, typedefs), 32u);
}

}  // namespace
