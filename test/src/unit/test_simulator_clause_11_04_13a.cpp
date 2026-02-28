// §11.4.13: for an explanation of range list syntax.

#include <cstring>

#include "parser/ast.h"
#include "simulator/eval.h"
#include "simulator/sim_context.h"  // StructTypeInfo, StructFieldInfo

#include "fixture_simulator.h"
#include "builders_ast.h"

using namespace delta;

static Expr* MakeRange(Arena& arena, Expr* lo, Expr* hi,
                       TokenKind op = TokenKind::kEof) {
  auto* r = arena.Create<Expr>();
  r->kind = ExprKind::kSelect;
  r->index = lo;
  r->index_end = hi;
  r->op = op;
  return r;
}

static Expr* MakeDollar(Arena& arena) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = "$";
  return e;
}
namespace {

TEST(EvalAdv, InsideDollarLowerBound) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("dv", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 5);
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "dv");
  inside->elements.push_back(
      MakeRange(f.arena, MakeDollar(f.arena), MakeInt(f.arena, 10)));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalAdv, InsideDollarUpperBound) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("du", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 200);
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "du");
  inside->elements.push_back(
      MakeRange(f.arena, MakeInt(f.arena, 100), MakeDollar(f.arena)));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

}  // namespace
