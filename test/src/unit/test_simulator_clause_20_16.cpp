// §20.16: Programmable logic array modeling system tasks


#include "parser/ast.h"
#include "simulation/eval.h"

#include "fixture_simulator.h"

using namespace delta;

static Expr* MkSysCall(Arena& arena, std::string_view name,
                       std::vector<Expr*> args) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kSystemCall;
  e->callee = name;
  e->args = std::move(args);
  return e;
}

namespace {

TEST(SysTask, AsyncAndArrayReturnsZero) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$async$and$array", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
