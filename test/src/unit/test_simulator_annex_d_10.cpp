#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

// Build a two-level hierarchical reference "scope.field" as a member-access
// expression, matching how the parser shapes a dotted name.
Expr* MkMember(Arena& arena, std::string_view scope, std::string_view field) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kMemberAccess;
  e->lhs = MkId(arena, scope);
  e->rhs = MkId(arena, field);
  return e;
}

// Annex D.10: $scale converts a time value from the source module's time unit
// to the invoking module's. A value held in a module whose unit (1 ns) is
// coarser than the invoking module's unit (1 ps) is multiplied by the ratio of
// the two units, so 5 (ns) becomes 5000 (ps).
TEST(OptionalScaleSim, ConvertsFromCoarserSourceUnit) {
  SysTaskFixture f;
  MakeVar(f, "src.d", 64, 5);
  f.ctx.SetScopeTimeScale("src", TimeScale{TimeUnit::kNs, 1, TimeUnit::kNs, 1});
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kPs, 1, TimeUnit::kPs, 1});
  auto* call = MkSysCall(f.arena, "$scale", {MkMember(f.arena, "src", "d")});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 5000u);
}

// Annex D.10: when the source module's unit (1 ps) is finer than the invoking
// module's unit (1 ns), the value shrinks by the same ratio, so 5000 (ps)
// becomes 5 (ns).
TEST(OptionalScaleSim, ConvertsFromFinerSourceUnit) {
  SysTaskFixture f;
  MakeVar(f, "src.d", 64, 5000);
  f.ctx.SetScopeTimeScale("src", TimeScale{TimeUnit::kPs, 1, TimeUnit::kPs, 1});
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kNs, 1, TimeUnit::kNs, 1});
  auto* call = MkSysCall(f.arena, "$scale", {MkMember(f.arena, "src", "d")});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 5u);
}

// Annex D.10: when the source and invoking modules share the same time unit the
// ratio is one, so the value is carried across unchanged.
TEST(OptionalScaleSim, EqualUnitsPassThrough) {
  SysTaskFixture f;
  MakeVar(f, "src.d", 64, 42);
  f.ctx.SetScopeTimeScale("src", TimeScale{TimeUnit::kNs, 1, TimeUnit::kNs, 1});
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kNs, 1, TimeUnit::kNs, 1});
  auto* call = MkSysCall(f.arena, "$scale", {MkMember(f.arena, "src", "d")});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 42u);
}

// Annex D.10: the argument is a complete hierarchical name, so the source
// module's time unit is taken from the entire hierarchy above the value. Here
// that hierarchy is the two-level scope "top.sub" (1 us), and converting into
// the invoking module's 1 ns unit multiplies by 1000, so 3 becomes 3000.
TEST(OptionalScaleSim, MultiLevelHierarchicalNameSelectsSourceScope) {
  SysTaskFixture f;
  MakeVar(f, "top.sub.d", 64, 3);
  f.ctx.SetScopeTimeScale("top.sub",
                          TimeScale{TimeUnit::kUs, 1, TimeUnit::kUs, 1});
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kNs, 1, TimeUnit::kNs, 1});
  auto* arg = f.arena.Create<Expr>();
  arg->kind = ExprKind::kMemberAccess;
  arg->lhs = MkMember(f.arena, "top", "sub");
  arg->rhs = MkId(f.arena, "d");
  auto* call = MkSysCall(f.arena, "$scale", {arg});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 3000u);
}

// Annex D.10: the unit ratio honors an off-decade magnitude. A source unit of
// 100 ns sits two base-10 orders above a 1 ns invoking unit, so the value is
// multiplied by 100: 2 becomes 200.
TEST(OptionalScaleSim, OffDecadeMagnitudeAffectsRatio) {
  SysTaskFixture f;
  MakeVar(f, "src.d", 64, 2);
  f.ctx.SetScopeTimeScale("src",
                          TimeScale{TimeUnit::kNs, 100, TimeUnit::kNs, 1});
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kNs, 1, TimeUnit::kNs, 1});
  auto* call = MkSysCall(f.arena, "$scale", {MkMember(f.arena, "src", "d")});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 200u);
}

// Annex D.10: a bare (non-hierarchical) name has no enclosing source module
// distinct from the invoker, so no conversion takes place even when the
// invoking module's unit differs from the design default.
TEST(OptionalScaleSim, BareNameHasNoSourceModuleSoPassesThrough) {
  SysTaskFixture f;
  MakeVar(f, "d", 64, 7);
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kPs, 1, TimeUnit::kPs, 1});
  auto* call = MkSysCall(f.arena, "$scale", {MkId(f.arena, "d")});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 7u);
}

// Annex D.10 (edge case): the argument is hierarchical, but its named source
// scope has no established time unit. With no source unit there is no ratio to
// apply, so the value is carried across unchanged even though the invoking
// module's unit differs from the design default.
TEST(OptionalScaleSim, UnknownSourceScopePassesThrough) {
  SysTaskFixture f;
  MakeVar(f, "ghost.d", 64, 9);
  // No SetScopeTimeScale for "ghost"; only the invoking unit is set.
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kPs, 1, TimeUnit::kPs, 1});
  auto* call = MkSysCall(f.arena, "$scale", {MkMember(f.arena, "ghost", "d")});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 9u);
}

// Annex D.10 (edge case): converting into a coarser unit divides, and the
// result is an integer time value, so a value that does not divide evenly is
// truncated toward zero. 1500 ps under a 1 ns invoking unit yields 1, not 2.
TEST(OptionalScaleSim, FinerSourceTruncatesTowardZero) {
  SysTaskFixture f;
  MakeVar(f, "src.d", 64, 1500);
  f.ctx.SetScopeTimeScale("src", TimeScale{TimeUnit::kPs, 1, TimeUnit::kPs, 1});
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kNs, 1, TimeUnit::kNs, 1});
  auto* call = MkSysCall(f.arena, "$scale", {MkMember(f.arena, "src", "d")});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 1u);
}

// Annex D.10 (degenerate input): a $scale call with no argument names no time
// value to convert, so the evaluator yields zero rather than faulting.
TEST(OptionalScaleSim, MissingArgumentYieldsZero) {
  SysTaskFixture f;
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kNs, 1, TimeUnit::kNs, 1});
  auto* call = MkSysCall(f.arena, "$scale", {});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 0u);
}

}  // namespace
