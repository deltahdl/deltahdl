// §11.4.6: Wildcard equality operators

#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/eval_array.h"

#include "fixture_simulator.h"
#include "builders_ast.h"
#include "helpers_eval_op.h"

using namespace delta;

// =============================================================================
// Helper fixture
// =============================================================================
static Expr* MkEq(Arena& arena, std::string_view a, std::string_view b) {
  auto* expr = arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kEqEq;
  auto* lhs = arena.Create<Expr>();
  lhs->kind = ExprKind::kIdentifier;
  lhs->text = a;
  auto* rhs = arena.Create<Expr>();
  rhs->kind = ExprKind::kIdentifier;
  rhs->text = b;
  expr->lhs = lhs;
  expr->rhs = rhs;
  return expr;
}

namespace {

TEST(EvalOpXZ, WildcardEqLeftX) {
  SimFixture f;
  // §11.4.6: 4'bx001 ==? 4'b0001 → x (left X in non-wildcard position)
  MakeVar4(f, "wl", 4, 0b0001, 0b1000);  // bit3=x
  auto* b = f.ctx.CreateVariable("wr", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 0b0001);
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqQuestion,
                          MakeId(f.arena, "wl"), MakeId(f.arena, "wr"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);  // result is X
}

// § binary_operator — ==? (wildcard equality)
TEST(SimA86, BinaryWildcardEq) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd5 ==? 8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// § binary_operator — !=? (wildcard inequality)
TEST(SimA86, BinaryWildcardNeq) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd5 !=? 8'd3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

}  // namespace
