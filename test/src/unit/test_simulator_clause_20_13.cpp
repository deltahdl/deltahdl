// §20.13: Coverage system functions

#include "parser/ast.h"
#include "simulation/coverage.h"
#include "simulation/eval.h"

#include "fixture_simulator.h"
#include "builders_systask.h"

using namespace delta;

namespace {

TEST(SysTask, CoverageControlReturnsZero) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$coverage_control",
                         {MkInt(f.arena, 1), MkInt(f.arena, 1),
                          MkInt(f.arena, 0), MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SysTask, CoverageGetMaxReturnsZero) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$coverage_get_max",
                         {MkInt(f.arena, 1), MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SysTask, CoverageGetReturnsZero) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$coverage_get",
                         {MkInt(f.arena, 1), MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SysTask, CoverageMergeReturnsZero) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$coverage_merge", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SysTask, CoverageSaveReturnsZero) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$coverage_save", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// =============================================================================
// S19.9: $get_coverage system function
// =============================================================================
TEST(Coverage, GlobalCoverageSingleGroup) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin b;
  b.name = "b0";
  b.values = {0};
  CoverageDB::AddBin(cp, b);

  db.Sample(g, {{"x", 0}});
  EXPECT_DOUBLE_EQ(db.GetGlobalCoverage(), 100.0);
}

}  // namespace
