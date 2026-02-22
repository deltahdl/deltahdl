// §20.13: Coverage system functions

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

#include "simulation/coverage.h"

using namespace delta;

struct SysTaskFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static Expr *MkSysCall(Arena &arena, std::string_view name,
                       std::vector<Expr *> args) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kSystemCall;
  e->callee = name;
  e->args = std::move(args);
  return e;
}

static Expr *MkInt(Arena &arena, uint64_t val) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

namespace {

TEST(SysTask, CoverageControlReturnsZero) {
  SysTaskFixture f;
  auto *expr = MkSysCall(f.arena, "$coverage_control",
                         {MkInt(f.arena, 1), MkInt(f.arena, 1),
                          MkInt(f.arena, 0), MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SysTask, CoverageGetMaxReturnsZero) {
  SysTaskFixture f;
  auto *expr = MkSysCall(f.arena, "$coverage_get_max",
                         {MkInt(f.arena, 1), MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SysTask, CoverageGetReturnsZero) {
  SysTaskFixture f;
  auto *expr = MkSysCall(f.arena, "$coverage_get",
                         {MkInt(f.arena, 1), MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SysTask, CoverageMergeReturnsZero) {
  SysTaskFixture f;
  auto *expr = MkSysCall(f.arena, "$coverage_merge", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SysTask, CoverageSaveReturnsZero) {
  SysTaskFixture f;
  auto *expr = MkSysCall(f.arena, "$coverage_save", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// =============================================================================
// S19.9: $get_coverage system function
// =============================================================================
TEST(Coverage, GlobalCoverageSingleGroup) {
  CoverageDB db;
  auto *g = db.CreateGroup("cg");
  auto *cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin b;
  b.name = "b0";
  b.values = {0};
  CoverageDB::AddBin(cp, b);

  db.Sample(g, {{"x", 0}});
  EXPECT_DOUBLE_EQ(db.GetGlobalCoverage(), 100.0);
}

} // namespace
