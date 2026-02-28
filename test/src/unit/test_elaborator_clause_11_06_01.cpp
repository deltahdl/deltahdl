// §11.6.1: Rules for expression bit lengths

#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(Elaboration, WidthInference_BinaryMax) {
  TypedefMap typedefs;
  Expr lhs;
  lhs.kind = ExprKind::kIntegerLiteral;
  lhs.int_val = 10;
  Expr rhs;
  rhs.kind = ExprKind::kIntegerLiteral;
  rhs.int_val = 20;
  Expr binop;
  binop.kind = ExprKind::kBinary;
  binop.op = TokenKind::kPlus;
  binop.lhs = &lhs;
  binop.rhs = &rhs;
  EXPECT_EQ(InferExprWidth(&binop, typedefs), 32);
}

TEST(Elaboration, WidthInference_ComparisonOneBit) {
  TypedefMap typedefs;
  Expr lhs;
  lhs.kind = ExprKind::kIntegerLiteral;
  lhs.int_val = 10;
  Expr rhs;
  rhs.kind = ExprKind::kIntegerLiteral;
  rhs.int_val = 20;
  Expr cmp;
  cmp.kind = ExprKind::kBinary;
  cmp.op = TokenKind::kEqEq;
  cmp.lhs = &lhs;
  cmp.rhs = &rhs;
  EXPECT_EQ(InferExprWidth(&cmp, typedefs), 1);
}

}  // namespace
