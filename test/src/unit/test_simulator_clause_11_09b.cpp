// §11.9: Tagged union expressions and member access


#include "lexer/token.h"
#include "parser/ast.h"
#include "simulation/eval.h"

#include "fixture_simulator.h"

using namespace delta;

// Shared fixture for expression evaluation tests.
// Helper: build an identifier Expr node.
static Expr* MakeId(Arena& arena, std::string_view name) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

namespace {

// ==========================================================================
// Member access (struct_var.field)
// ==========================================================================
TEST(EvalOp, MemberAccessBasic) {
  SimFixture f;
  // Simulate a struct with a 32-bit field stored as a variable "s.x".
  auto* var = f.ctx.CreateVariable("s.x", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 99);

  auto* acc = f.arena.Create<Expr>();
  acc->kind = ExprKind::kMemberAccess;
  acc->lhs = MakeId(f.arena, "s");
  acc->rhs = MakeId(f.arena, "x");

  auto result = EvalExpr(acc, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 99u);
}

}  // namespace
