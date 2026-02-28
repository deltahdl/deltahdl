// §11.5: Operands


#include "simulator/eval.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(Eval, VariableLookup) {
  ExprFixture f;
  auto* var = f.ctx.CreateVariable("myvar", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 123);

  // Create an identifier expression manually.
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kIdentifier;
  expr->text = "myvar";
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 123u);
}

}  // namespace
