#include <cstring>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/adv_sim.h"
#include "simulator/eval.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

TEST(EvalAdv, AssignInExprBasic) {
  SimFixture f;

  MakeVar(f, "aie", 32, 0);
  auto* assign = f.arena.Create<Expr>();
  assign->kind = ExprKind::kBinary;
  assign->op = TokenKind::kEq;
  assign->lhs = MakeId(f.arena, "aie");
  assign->rhs = MakeInt(f.arena, 42);
  auto result = EvalExpr(assign, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
  auto* var = f.ctx.FindVariable("aie");
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(EvalAdv, AssignInExprTruncToLHSWidth) {
  SimFixture f;

  MakeVar(f, "aie8", 8, 0);
  auto* assign = f.arena.Create<Expr>();
  assign->kind = ExprKind::kBinary;
  assign->op = TokenKind::kEq;
  assign->lhs = MakeId(f.arena, "aie8");
  assign->rhs = MakeInt(f.arena, 0x1FF);
  auto result = EvalExpr(assign, f.ctx, f.arena);

  EXPECT_EQ(result.width, 8u);
  EXPECT_EQ(result.ToUint64(), 0xFFu);
}

}
