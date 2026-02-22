// §11.4.13: for an explanation of range list syntax.

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h" // StructTypeInfo, StructFieldInfo
#include <cstring>
#include <gtest/gtest.h>

using namespace delta;

// Shared fixture for advanced expression evaluation tests (§11 phases 22+).
struct EvalAdvFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static Expr *MakeInt(Arena &arena, uint64_t val) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

static Expr *MakeId(Arena &arena, std::string_view name) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

static Expr *MakeRange(Arena &arena, Expr *lo, Expr *hi,
                       TokenKind op = TokenKind::kEof) {
  auto *r = arena.Create<Expr>();
  r->kind = ExprKind::kSelect;
  r->index = lo;
  r->index_end = hi;
  r->op = op;
  return r;
}

static Expr *MakeDollar(Arena &arena) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = "$";
  return e;
}
namespace {

TEST(EvalAdv, InsideDollarLowerBound) {
  EvalAdvFixture f;
  auto *var = f.ctx.CreateVariable("dv", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 5);
  auto *inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "dv");
  inside->elements.push_back(
      MakeRange(f.arena, MakeDollar(f.arena), MakeInt(f.arena, 10)));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalAdv, InsideDollarUpperBound) {
  EvalAdvFixture f;
  auto *var = f.ctx.CreateVariable("du", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 200);
  auto *inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "du");
  inside->elements.push_back(
      MakeRange(f.arena, MakeInt(f.arena, 100), MakeDollar(f.arena)));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

} // namespace
