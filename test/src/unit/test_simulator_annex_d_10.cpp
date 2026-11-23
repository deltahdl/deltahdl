#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "builders_systask.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_annex_d_call_forms.h"
#include "helpers_preprocess_and_get.h"
#include "helpers_reported_error.h"
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

std::string ChildUnderTop(const std::string& child_unit,
                          const std::string& child_decl,
                          const std::string& top_unit,
                          const std::string& top_body) {
  std::string src = "module child;\n  timeunit ";
  src += child_unit;
  src += ";\n";
  src += child_decl;
  src += "endmodule\nmodule top;\n  timeunit ";
  src += top_unit;
  src += ";\n  child c1();\n";
  src += top_body;
  src += "endmodule\n";
  return src;
}

std::string ScaledChildValue(const std::string& child_unit,
                             const std::string& child_decl,
                             const std::string& top_unit,
                             const std::string& arg) {
  std::string body = "  initial #1 $display(\"%0d\", $scale(";
  body += arg;
  body += "));\n";
  SimFixture f;
  return RunCapture(ChildUnderTop(child_unit, child_decl, top_unit, body), f);
}

TEST(OptionalScaleSim, AFinerSourceUnitDividesInADesign) {
  EXPECT_EQ(ScaledChildValue("1ps / 1ps", "  integer d = 5000;\n", "1ns / 1ps",
                             "c1.d"),
            "5\n");
}

TEST(OptionalScaleSim, EqualUnitsLeaveTheValueInADesign) {
  EXPECT_EQ(
      ScaledChildValue("1ns / 1ps", "  integer d = 42;\n", "1ns / 1ps", "c1.d"),
      "42\n");
}

TEST(OptionalScaleSim, AnOffDecadeUnitSetsTheRatioInADesign) {
  EXPECT_EQ(ScaledChildValue("100ns / 1ns", "  integer d = 2;\n", "1ns / 1ns",
                             "c1.d"),
            "200\n");
}

TEST(OptionalScaleSim, ATimeVariableConverts) {
  EXPECT_EQ(
      ScaledChildValue("1ns / 1ps", "  time d = 5;\n", "1ps / 1ps", "c1.d"),
      "5000\n");
}

TEST(OptionalScaleSim, DISABLED_ARootPathConverts) {
  EXPECT_EQ(ScaledChildValue("1ns / 1ps", "  integer d = 5;\n", "1ps / 1ps",
                             "$root.top.c1.d"),
            "5000\n");
}

TEST(OptionalScaleSim, DISABLED_AValueInAGenerateBlockConverts) {
  EXPECT_EQ(ScaledChildValue("1ns / 1ps",
                             "  if (1) begin : blk\n    integer e = 6;\n"
                             "  end\n",
                             "1ps / 1ps", "c1.blk.e"),
            "6000\n");
}

TEST(OptionalScaleSim, DISABLED_ARealOrRealtimeValueConvertsItsValue) {
  SimFixture f;
  std::string out = RunCapture(
      ChildUnderTop("1ns / 1ps", "  real r = 1.5;\n  realtime rt = 2.5;\n",
                    "1ps / 1ps",
                    "  initial #1 $display(\"%0d %0d\", $scale(c1.r), "
                    "$scale(c1.rt));\n"),
      f);
  EXPECT_EQ(out, "1500 2500\n");
}

TEST(OptionalScaleSim, ANameInTheCallingModuleIsUnchangedInADesign) {
  SimFixture f;
  std::string out = RunCapture(
      "module top;\n"
      "  timeunit 1ps / 1ps;\n"
      "  integer d = 7;\n"
      "  initial #1 $display(\"%0d\", $scale(d));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "7\n");
}

TEST(OptionalScaleSim, AnInterfaceValueConvertsFromTheInterfaceUnit) {
  SimFixture f;
  std::string out = RunCapture(
      "interface ifc;\n"
      "  timeunit 1ns / 1ps;\n"
      "  integer d = 4;\n"
      "endinterface\n"
      "module top;\n"
      "  timeunit 1ps / 1ps;\n"
      "  ifc i1();\n"
      "  initial #1 $display(\"%0d\", $scale(i1.d));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4000\n");
}

TEST(OptionalScaleSim, AFunctionOrTaskConvertsIntoItsModuleUnit) {
  SimFixture f;
  std::string out =
      RunCapture(ChildUnderTop("1ns / 1ps", "  integer d = 5;\n", "1ps / 1ps",
                               "  function automatic longint fn();\n"
                               "    return $scale(c1.d);\n"
                               "  endfunction\n"
                               "  task automatic tk();\n"
                               "    $display(\"%0d\", $scale(c1.d));\n"
                               "  endtask\n"
                               "  initial #1 begin\n"
                               "    $display(\"%0d\", fn());\n"
                               "    tk();\n"
                               "  end\n"),
                 f);
  EXPECT_EQ(out, "5000\n5000\n");
}

TEST(OptionalScaleSim, AProgramOrInterfaceConvertsIntoItsOwnUnit) {
  SimFixture f;
  std::string out = RunCapture(
      "module child;\n"
      "  timeunit 1ns / 1ps;\n"
      "  integer d = 5;\n"
      "endmodule\n"
      "program prg;\n"
      "  timeunit 1ps / 1ps;\n"
      "  initial #2 $display(\"%0d\", $scale(top.c1.d));\n"
      "endprogram\n"
      "interface ifc;\n"
      "  timeunit 1ps / 1ps;\n"
      "  initial #1 $display(\"%0d\", $scale(top.c1.d));\n"
      "endinterface\n"
      "module top;\n"
      "  timeunit 10ps / 1ps;\n"
      "  child c1();\n"
      "  prg p1();\n"
      "  ifc i1();\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "5000\n5000\n");
}

TEST(OptionalScaleSim, TimescaleDirectiveUnitsConvert) {
  SimFixture f;
  std::string out = PreprocessAndCapture(
      "`timescale 1ns / 1ps\n"
      "module child;\n"
      "  integer d = 5;\n"
      "endmodule\n"
      "`timescale 1ps / 1ps\n"
      "module top;\n"
      "  child c1();\n"
      "  initial #1 $display(\"%0d\", $scale(c1.d));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "5000\n");
}

TEST(OptionalScaleSim, TheResultFeedsProceduralAndContinuousAssignments) {
  SimFixture f;
  std::string out =
      RunCapture(ChildUnderTop("1ns / 1ps", "  integer d = 5;\n", "1ps / 1ps",
                               "  longint a;\n"
                               "  wire [63:0] w = $scale(c1.d);\n"
                               "  initial #1 begin\n"
                               "    a = $scale(c1.d);\n"
                               "    #1 $display(\"%0d %0d\", a, w);\n"
                               "  end\n"),
                 f);
  EXPECT_EQ(out, "5000 5000\n");
}

constexpr const char* kScaleForm =
    "$scale is written with one hierarchical name as its argument, and this "
    "call is not";

TEST(OptionalScaleForm, DISABLED_NoArgumentListIsReported) {
  ExpectOnlyTheMalformedCallReported("v = $scale(t.v)", "v = $scale",
                                     kScaleForm, "D.10");
}

TEST(OptionalScaleForm, DISABLED_AnEmptyArgumentListIsReported) {
  ExpectOnlyTheMalformedCallReported("v = $scale(t.v)", "v = $scale()",
                                     kScaleForm, "D.10");
}

TEST(OptionalScaleForm, DISABLED_TwoArgumentsAreReported) {
  ExpectOnlyTheMalformedCallReported("v = $scale(t.v)", "v = $scale(t.v, t.v)",
                                     kScaleForm, "D.10");
}

TEST(OptionalScaleForm, DISABLED_AnArgumentThatIsNoNameIsReported) {
  for (const char* malformed : {"v = $scale(3)", "v = $scale(t.v + 1)"}) {
    ExpectOnlyTheMalformedCallReported("v = $scale(t.v)", malformed, kScaleForm,
                                       "D.10");
  }
}

TEST(OptionalScaleForm, ARootOrGenerateBlockNameIsAcceptedWithoutAReport) {
  for (const char* arg : {"$root.top.c1.d", "c1.blk.e"}) {
    std::string body = "  initial #1 $display(\"%0d\", $scale(";
    body += arg;
    body += "));\n";
    SimFixture f;
    RunCapture(ChildUnderTop("1ns / 1ps",
                             "  integer d = 5;\n  if (1) begin : blk\n"
                             "    integer e = 6;\n  end\n",
                             "1ps / 1ps", body),
               f);
    EXPECT_FALSE(f.diag.HasErrors()) << arg;
  }
}

TEST(OptionalScaleForm, ANameResolvingToNoObjectKeepsTheReferenceReport) {
  std::string src =
      ChildUnderTop("1ns / 1ps", "  integer d = 5;\n", "1ps / 1ps",
                    "  initial #1 $display(\"%0d\", $scale(c1.nosuch));\n");
  SimFixture f;
  RunCapture(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference 'c1.nosuch' is unresolved: "
                            "'nosuch' is not declared in module 'child'",
                            LineHolding(src, "c1.nosuch"), "23.6"));
}

}  // namespace
