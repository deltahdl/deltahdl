// §11.5: Operands

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

using namespace delta;

struct ExprFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

namespace {

TEST(Eval, VariableLookup) {
  ExprFixture f;
  auto *var = f.ctx.CreateVariable("myvar", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 123);

  // Create an identifier expression manually.
  auto *expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kIdentifier;
  expr->text = "myvar";
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 123u);
}

}  // namespace
