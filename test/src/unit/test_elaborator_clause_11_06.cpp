#include "common/types.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "lexer/token.h"
#include "parser/ast.h"

using namespace delta;

namespace {

// Builds a binary plus expression of two 16-bit integer literals
// ("16'h0 + 16'h0") in the given arena, returning the plus node.
static Expr* MakeSixteenBitAddition(Arena& arena) {
  auto* a = arena.Create<Expr>();
  a->kind = ExprKind::kIntegerLiteral;
  a->text = "16'h0";
  auto* b = arena.Create<Expr>();
  b->kind = ExprKind::kIntegerLiteral;
  b->text = "16'h0";
  auto* plus = arena.Create<Expr>();
  plus->kind = ExprKind::kBinary;
  plus->op = TokenKind::kPlus;
  plus->lhs = a;
  plus->rhs = b;
  return plus;
}

TEST(AdditionBitLength, WidensToLhsWhenLhsWiderThanOperands) {
  Arena arena;
  TypedefMap typedefs;
  Expr* plus = MakeSixteenBitAddition(arena);

  EXPECT_EQ(ContextWidth(plus, 17u, typedefs), 17u);
}

TEST(AdditionBitLength, KeepsWidestOperandWhenLhsNarrower) {
  Arena arena;
  TypedefMap typedefs;
  Expr* plus = MakeSixteenBitAddition(arena);

  EXPECT_EQ(ContextWidth(plus, 8u, typedefs), 16u);
}

TEST(AdditionBitLength, AssignmentToWiderLhsIsAcceptedByElaborator) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [15:0] a, b;\n"
             "  logic [16:0] sumB;\n"
             "  initial sumB = a + b;\n"
             "endmodule\n"));
}

}  // namespace
