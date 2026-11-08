#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "builders_systask.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "parser/ast_expr.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

Expr* MkMember(Arena& arena, std::string_view scope, std::string_view field) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kMemberAccess;
  e->lhs = MkId(arena, scope);
  e->rhs = MkId(arena, field);
  return e;
}

TEST(OptionalScaleSim, ConvertsFromCoarserSourceUnit) {
  SysTaskFixture f;
  MakeVar(f, "src.d", 64, 5);
  f.ctx.SetScopeTimeScale("src", TimeScale{TimeUnit::kNs, 1, TimeUnit::kNs, 1});
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kPs, 1, TimeUnit::kPs, 1});
  auto* call = MkSysCall(f.arena, "$scale", {MkMember(f.arena, "src", "d")});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 5000u);
}

TEST(OptionalScaleSim, ConvertsFromFinerSourceUnit) {
  SysTaskFixture f;
  MakeVar(f, "src.d", 64, 5000);
  f.ctx.SetScopeTimeScale("src", TimeScale{TimeUnit::kPs, 1, TimeUnit::kPs, 1});
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kNs, 1, TimeUnit::kNs, 1});
  auto* call = MkSysCall(f.arena, "$scale", {MkMember(f.arena, "src", "d")});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 5u);
}

TEST(OptionalScaleSim, EqualUnitsPassThrough) {
  SysTaskFixture f;
  MakeVar(f, "src.d", 64, 42);
  f.ctx.SetScopeTimeScale("src", TimeScale{TimeUnit::kNs, 1, TimeUnit::kNs, 1});
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kNs, 1, TimeUnit::kNs, 1});
  auto* call = MkSysCall(f.arena, "$scale", {MkMember(f.arena, "src", "d")});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 42u);
}

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

TEST(OptionalScaleSim, OffDecadeMagnitudeAffectsRatio) {
  SysTaskFixture f;
  MakeVar(f, "src.d", 64, 2);
  f.ctx.SetScopeTimeScale("src",
                          TimeScale{TimeUnit::kNs, 100, TimeUnit::kNs, 1});
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kNs, 1, TimeUnit::kNs, 1});
  auto* call = MkSysCall(f.arena, "$scale", {MkMember(f.arena, "src", "d")});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 200u);
}

TEST(OptionalScaleSim, BareNameHasNoSourceModuleSoPassesThrough) {
  SysTaskFixture f;
  MakeVar(f, "d", 64, 7);
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kPs, 1, TimeUnit::kPs, 1});
  auto* call = MkSysCall(f.arena, "$scale", {MkId(f.arena, "d")});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 7u);
}

TEST(OptionalScaleSim, UnknownSourceScopePassesThrough) {
  SysTaskFixture f;
  MakeVar(f, "ghost.d", 64, 9);
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kPs, 1, TimeUnit::kPs, 1});
  auto* call = MkSysCall(f.arena, "$scale", {MkMember(f.arena, "ghost", "d")});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 9u);
}

TEST(OptionalScaleSim, FinerSourceTruncatesTowardZero) {
  SysTaskFixture f;
  MakeVar(f, "src.d", 64, 1500);
  f.ctx.SetScopeTimeScale("src", TimeScale{TimeUnit::kPs, 1, TimeUnit::kPs, 1});
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kNs, 1, TimeUnit::kNs, 1});
  auto* call = MkSysCall(f.arena, "$scale", {MkMember(f.arena, "src", "d")});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 1u);
}

TEST(OptionalScaleSim, MissingArgumentYieldsZero) {
  SysTaskFixture f;
  f.ctx.SetCurrentTimeScale(TimeScale{TimeUnit::kNs, 1, TimeUnit::kNs, 1});
  auto* call = MkSysCall(f.arena, "$scale", {});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 0u);
}

TEST(OptionalScaleSim, ConvertsAChildInstanceValueIntoTheInvokingTopUnit) {
  SimFixture f;
  std::string out = RunCapture(
      "module child;\n"
      "  timeunit 1ns / 1ps;\n"
      "  integer d = 5;\n"
      "endmodule\n"
      "module top;\n"
      "  timeunit 1ps / 1ps;\n"
      "  child c1();\n"
      "  initial #1 $display(\"%0d\", $scale(c1.d));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "5000\n");
}

TEST(OptionalScaleSim, AnInstanceInvokingScaleConvertsIntoItsOwnUnit) {
  SimFixture f;
  std::string out = RunCapture(
      "module child;\n"
      "  timeunit 1ps / 1ps;\n"
      "  initial #1 $display(\"%0d\", $scale(top.d));\n"
      "endmodule\n"
      "module top;\n"
      "  timeunit 1ns / 1ps;\n"
      "  integer d = 7;\n"
      "  child c1();\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "7000\n");
}

TEST(OptionalScaleSim, ThePathAboveTheValueNamesTheSourceModule) {
  SimFixture f;
  std::string out = RunCapture(
      "module leaf;\n"
      "  timeunit 1us / 1ns;\n"
      "  integer d = 3;\n"
      "endmodule\n"
      "module mid;\n"
      "  timeunit 1ns / 1ns;\n"
      "  leaf l1();\n"
      "endmodule\n"
      "module top;\n"
      "  timeunit 1ns / 1ns;\n"
      "  mid m1();\n"
      "  initial #1 begin\n"
      "    $display(\"%0d\", $scale(m1.l1.d));\n"
      "    $display(\"%0d\", $scale(top.m1.l1.d));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3000\n3000\n");
}

}  // namespace
