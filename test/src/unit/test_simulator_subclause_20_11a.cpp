#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "builders_systask.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/sva_engine_queues.h"

using namespace delta;

namespace {

TEST(SysTask, AssertOnDoesNotCrash) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$asserton", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(SysTask, AssertOffDoesNotCrash) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$assertoff", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(SysTask, AssertKillDoesNotCrash) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$assertkill", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(SysTask, AssertControlDoesNotCrash) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$assertcontrol", {MkInt(f.arena, 3)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(SvaEngine, AssertionControlDefaultOn) {
  AssertionControl ctrl;
  EXPECT_TRUE(ctrl.IsEnabled("inst1"));
  EXPECT_TRUE(ctrl.IsEnabled("inst2"));
}

TEST(SvaEngine, AssertoffDisablesInstance) {
  AssertionControl ctrl;
  ctrl.SetOff("inst1");
  EXPECT_FALSE(ctrl.IsEnabled("inst1"));
  EXPECT_TRUE(ctrl.IsEnabled("inst2"));
}

TEST(SvaEngine, AssertControlGlobalOff) {
  AssertionControl ctrl;
  ctrl.SetGlobalOff();
  EXPECT_FALSE(ctrl.IsEnabled("any_instance"));
  EXPECT_FALSE(ctrl.IsEnabled("another_inst"));
}

TEST(SvaEngine, AssertControlGlobalOn) {
  AssertionControl ctrl;
  ctrl.SetGlobalOff();
  ctrl.SetGlobalOn();
  EXPECT_TRUE(ctrl.IsEnabled("any_instance"));
}

TEST(SvaEngine, AssertPassOff) {
  AssertionControl ctrl;
  EXPECT_TRUE(ctrl.IsPassEnabled("inst1"));
  ctrl.SetPassOff("inst1");
  EXPECT_FALSE(ctrl.IsPassEnabled("inst1"));
  EXPECT_TRUE(ctrl.IsPassEnabled("inst2"));
}

struct SvaFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
  SvaEngine engine;
};

TEST(SvaEngine, AssertionControlIntegration) {
  SvaFixture f;
  bool executed = false;

  DeferredAssertion da;
  da.condition_val = 1;
  da.instance_name = "my_assert";
  da.pass_action = [&executed]() { executed = true; };

  f.engine.GetControl().SetOff("my_assert");
  f.engine.QueueDeferredAssertionIfEnabled(da);
  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_FALSE(executed);
}

TEST(SvaEngine, AssertionControlEnabledExecution) {
  SvaFixture f;
  bool executed = false;

  DeferredAssertion da;
  da.condition_val = 1;
  da.instance_name = "my_assert";
  da.pass_action = [&executed]() { executed = true; };

  f.engine.QueueDeferredAssertionIfEnabled(da);
  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_TRUE(executed);
}

TEST(SvaEngine, PassOffSkipsPassAction) {
  SvaFixture f;
  bool pass_called = false;

  DeferredAssertion da;
  da.condition_val = 1;
  da.instance_name = "check_a";
  da.pass_action = [&pass_called]() { pass_called = true; };

  f.engine.GetControl().SetPassOff("check_a");
  f.engine.QueueDeferredAssertionIfEnabled(da);
  f.engine.FlushDeferredAssertionsRespectingControl(f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_FALSE(pass_called);
}

TEST(SvaEngine, FailOffSkipsFailAction) {
  SvaFixture f;
  bool fail_called = false;

  DeferredAssertion da;
  da.condition_val = 0;
  da.instance_name = "check_b";
  da.fail_action = [&fail_called]() { fail_called = true; };

  f.engine.GetControl().SetFailOff("check_b");
  f.engine.QueueDeferredAssertionIfEnabled(da);
  f.engine.FlushDeferredAssertionsRespectingControl(f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_FALSE(fail_called);
}

TEST(SvaEngine, KillClearsPendingAssertions) {
  SvaFixture f;
  int count = 0;

  for (int i = 0; i < 3; ++i) {
    DeferredAssertion da;
    da.condition_val = 1;
    da.instance_name = "killed_inst";
    da.pass_action = [&count]() { ++count; };
    f.engine.QueueDeferredAssertion(da);
  }

  f.engine.KillAssertionsForInstance("killed_inst");
  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  f.scheduler.Run();
  EXPECT_EQ(count, 0);
}

TEST(SvaEngine, LockPreventsStatusChangeUntilUnlock) {
  AssertionControl ctrl;
  ctrl.Lock("inst1");
  ctrl.SetOff("inst1");
  EXPECT_TRUE(ctrl.IsEnabled("inst1"));
  ctrl.Unlock("inst1");
  ctrl.SetOff("inst1");
  EXPECT_FALSE(ctrl.IsEnabled("inst1"));
}

TEST(SvaEngine, UnlockReachesLockedAssertion) {
  AssertionControl ctrl;
  ctrl.ApplyControl(static_cast<int>(AssertControlType::kLock), "inst1");
  ctrl.ApplyControl(static_cast<int>(AssertControlType::kOff), "inst1");
  EXPECT_TRUE(ctrl.IsEnabled("inst1"));
  ctrl.ApplyControl(static_cast<int>(AssertControlType::kUnlock), "inst1");
  EXPECT_FALSE(ctrl.IsLocked("inst1"));
}

TEST(SvaEngine, ApplyControlOffOnByControlType) {
  AssertionControl ctrl;
  ctrl.ApplyControl(static_cast<int>(AssertControlType::kOff), "inst1");
  EXPECT_FALSE(ctrl.IsEnabled("inst1"));
  ctrl.ApplyControl(static_cast<int>(AssertControlType::kOn), "inst1");
  EXPECT_TRUE(ctrl.IsEnabled("inst1"));
}

TEST(SvaEngine, VacuousOffDisablesOnlyVacuousPass) {
  AssertionControl ctrl;
  ctrl.SetVacuousOff("inst1");
  EXPECT_FALSE(ctrl.IsVacuousPassEnabled("inst1"));
  EXPECT_TRUE(ctrl.IsNonvacuousPassEnabled("inst1"));
  ctrl.SetPassOn("inst1");
  EXPECT_TRUE(ctrl.IsVacuousPassEnabled("inst1"));
}

TEST(SvaEngine, NonvacuousOnReenablesNonvacuousPassOnly) {
  AssertionControl ctrl;
  ctrl.SetPassOff("inst1");
  EXPECT_FALSE(ctrl.IsNonvacuousPassEnabled("inst1"));
  ctrl.SetNonvacuousOn("inst1");
  EXPECT_TRUE(ctrl.IsNonvacuousPassEnabled("inst1"));
  EXPECT_FALSE(ctrl.IsVacuousPassEnabled("inst1"));
}

TEST(SvaEngine, OnlyStatusControlsAffectStatistics) {
  EXPECT_TRUE(
      ControlTypeAffectsStatistics(static_cast<int>(AssertControlType::kKill)));
  EXPECT_FALSE(ControlTypeAffectsStatistics(
      static_cast<int>(AssertControlType::kPassOn)));
  EXPECT_FALSE(ControlTypeAffectsStatistics(
      static_cast<int>(AssertControlType::kVacuousOff)));
}

TEST(SvaEngine, AssertOffEquivalentToControl) {
  AssertControlInvocation inv;
  ASSERT_TRUE(EquivalentAssertControlForTask("$assertoff", inv));
  EXPECT_EQ(inv.control_type, static_cast<uint32_t>(AssertControlType::kOff));
  EXPECT_EQ(inv.assertion_type, 15u);
  EXPECT_EQ(inv.directive_type, 7u);
}

TEST(SvaEngine, AssertFailOffEquivalentToControl) {
  AssertControlInvocation inv;
  ASSERT_TRUE(EquivalentAssertControlForTask("$assertfailoff", inv));
  EXPECT_EQ(inv.control_type,
            static_cast<uint32_t>(AssertControlType::kFailOff));
  EXPECT_EQ(inv.assertion_type, 31u);
}

TEST(SvaEngine, NonControlTaskHasNoEquivalent) {
  AssertControlInvocation inv;
  EXPECT_FALSE(EquivalentAssertControlForTask("$display", inv));
}

TEST(SvaEngine, ControlArgumentDefaults) {
  EXPECT_EQ(kAssertionTypeDefault, 255u);
  EXPECT_EQ(kDirectiveTypeDefault, 7u);
}

TEST(SvaEngine, ApplyControlPassOffPassOnByControlType) {
  AssertionControl ctrl;
  ctrl.ApplyControl(static_cast<int>(AssertControlType::kPassOff), "inst1");
  EXPECT_FALSE(ctrl.IsPassEnabled("inst1"));
  ctrl.ApplyControl(static_cast<int>(AssertControlType::kPassOn), "inst1");
  EXPECT_TRUE(ctrl.IsPassEnabled("inst1"));
}

TEST(SvaEngine, ApplyControlFailOffFailOnByControlType) {
  AssertionControl ctrl;
  ctrl.ApplyControl(static_cast<int>(AssertControlType::kFailOff), "inst1");
  EXPECT_FALSE(ctrl.IsFailEnabled("inst1"));
  ctrl.ApplyControl(static_cast<int>(AssertControlType::kFailOn), "inst1");
  EXPECT_TRUE(ctrl.IsFailEnabled("inst1"));
}

TEST(SvaEngine, ApplyControlVacuousOffNonvacuousOnByControlType) {
  AssertionControl ctrl;
  ctrl.ApplyControl(static_cast<int>(AssertControlType::kVacuousOff), "inst1");
  EXPECT_FALSE(ctrl.IsVacuousPassEnabled("inst1"));
  EXPECT_TRUE(ctrl.IsNonvacuousPassEnabled("inst1"));
  ctrl.ApplyControl(static_cast<int>(AssertControlType::kPassOff), "inst1");
  ctrl.ApplyControl(static_cast<int>(AssertControlType::kNonvacuousOn),
                    "inst1");
  EXPECT_TRUE(ctrl.IsNonvacuousPassEnabled("inst1"));
}

TEST(SvaEngine, ApplyControlKillByControlType) {
  AssertionControl ctrl;
  ctrl.ApplyControl(static_cast<int>(AssertControlType::kKill), "inst1");
  EXPECT_FALSE(ctrl.IsEnabled("inst1"));
  EXPECT_TRUE(ctrl.WasKilled("inst1"));
}

TEST(SvaEngine, StatusTaskEquivalents) {
  AssertControlInvocation inv;
  ASSERT_TRUE(EquivalentAssertControlForTask("$asserton", inv));
  EXPECT_EQ(inv.control_type, static_cast<uint32_t>(AssertControlType::kOn));
  EXPECT_EQ(inv.assertion_type, 15u);
  EXPECT_EQ(inv.directive_type, 7u);
  ASSERT_TRUE(EquivalentAssertControlForTask("$assertkill", inv));
  EXPECT_EQ(inv.control_type, static_cast<uint32_t>(AssertControlType::kKill));
  EXPECT_EQ(inv.assertion_type, 15u);
}

TEST(SvaEngine, ActionTaskEquivalents) {
  AssertControlInvocation inv;
  ASSERT_TRUE(EquivalentAssertControlForTask("$assertpasson", inv));
  EXPECT_EQ(inv.control_type,
            static_cast<uint32_t>(AssertControlType::kPassOn));
  EXPECT_EQ(inv.assertion_type, 31u);
  ASSERT_TRUE(EquivalentAssertControlForTask("$assertpassoff", inv));
  EXPECT_EQ(inv.control_type,
            static_cast<uint32_t>(AssertControlType::kPassOff));
  ASSERT_TRUE(EquivalentAssertControlForTask("$assertfailon", inv));
  EXPECT_EQ(inv.control_type,
            static_cast<uint32_t>(AssertControlType::kFailOn));
  ASSERT_TRUE(EquivalentAssertControlForTask("$assertnonvacuouson", inv));
  EXPECT_EQ(inv.control_type,
            static_cast<uint32_t>(AssertControlType::kNonvacuousOn));
  ASSERT_TRUE(EquivalentAssertControlForTask("$assertvacuousoff", inv));
  EXPECT_EQ(inv.control_type,
            static_cast<uint32_t>(AssertControlType::kVacuousOff));
}

TEST(SvaEngine, LockAlsoBlocksActionControls) {
  AssertionControl ctrl;
  ctrl.Lock("inst1");
  ctrl.SetPassOff("inst1");
  EXPECT_TRUE(ctrl.IsPassEnabled("inst1"));
  ctrl.SetFailOff("inst1");
  EXPECT_TRUE(ctrl.IsFailEnabled("inst1"));
  ctrl.Unlock("inst1");
  ctrl.SetPassOff("inst1");
  EXPECT_FALSE(ctrl.IsPassEnabled("inst1"));
}

TEST(SvaEngine, StatusControlsBelowSixAffectStatistics) {
  EXPECT_TRUE(
      ControlTypeAffectsStatistics(static_cast<int>(AssertControlType::kLock)));
  EXPECT_TRUE(
      ControlTypeAffectsStatistics(static_cast<int>(AssertControlType::kOn)));
  EXPECT_FALSE(ControlTypeAffectsStatistics(
      static_cast<int>(AssertControlType::kPassOff)));
}

TEST(SvaEngine, AssertionTypeMaskSelectsKinds) {
  uint32_t mask = static_cast<uint32_t>(AssertionTypeBit::kConcurrent) |
                  static_cast<uint32_t>(AssertionTypeBit::kSimpleImmediate);
  EXPECT_TRUE(ControlAffectsAssertionType(mask, AssertionTypeBit::kConcurrent));
  EXPECT_TRUE(
      ControlAffectsAssertionType(mask, AssertionTypeBit::kSimpleImmediate));
  EXPECT_FALSE(ControlAffectsAssertionType(
      mask, AssertionTypeBit::kObservedDeferredImmediate));
}

TEST(SvaEngine, DefaultAssertionTypeAffectsAllKinds) {
  EXPECT_TRUE(ControlAffectsAssertionType(kAssertionTypeDefault,
                                          AssertionTypeBit::kConcurrent));
  EXPECT_TRUE(ControlAffectsAssertionType(kAssertionTypeDefault,
                                          AssertionTypeBit::kExpect));
  EXPECT_TRUE(ControlAffectsAssertionType(kAssertionTypeDefault,
                                          AssertionTypeBit::kPriority));
}

TEST(SvaEngine, DirectiveTypeMaskSelectsDirectives) {
  uint32_t mask = static_cast<uint32_t>(DirectiveTypeBit::kAssert) |
                  static_cast<uint32_t>(DirectiveTypeBit::kCover);
  EXPECT_TRUE(ControlAffectsDirectiveType(mask, DirectiveTypeBit::kAssert));
  EXPECT_TRUE(ControlAffectsDirectiveType(mask, DirectiveTypeBit::kCover));
  EXPECT_FALSE(ControlAffectsDirectiveType(mask, DirectiveTypeBit::kAssume));
}

TEST(SvaEngine, DefaultDirectiveTypeAffectsAllDirectives) {
  EXPECT_TRUE(ControlAffectsDirectiveType(kDirectiveTypeDefault,
                                          DirectiveTypeBit::kAssert));
  EXPECT_TRUE(ControlAffectsDirectiveType(kDirectiveTypeDefault,
                                          DirectiveTypeBit::kCover));
  EXPECT_TRUE(ControlAffectsDirectiveType(kDirectiveTypeDefault,
                                          DirectiveTypeBit::kAssume));
}

int RunAndGetAssertionFailCount(const char* src) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design) return -1;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  return f.ctx.AssertionFailCount();
}

TEST(AssertControlSim, AssertOffStopsImmediateAssertionChecking) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    $assertoff;\n"
      "    assert(0);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.AssertionFailCount(), 0);
}

TEST(AssertControlSim, AssertOnReenablesImmediateAssertionChecking) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    $assertoff;\n"
      "    assert(0);\n"
      "    $asserton;\n"
      "    assert(0);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.AssertionFailCount(), 1);
}

TEST(AssertControlSim, AssertControlOffThenOnByControlType) {
  EXPECT_EQ(RunAndGetAssertionFailCount("module t;\n"
                                        "  initial begin\n"
                                        "    $assertcontrol(4);\n"
                                        "    assert(0);\n"
                                        "    $assertcontrol(3);\n"
                                        "    assert(0);\n"
                                        "  end\n"
                                        "endmodule\n"),
            1);
}

TEST(AssertControlSim, AssertionTypeMaskExcludesSimpleImmediate) {
  EXPECT_EQ(RunAndGetAssertionFailCount("module t;\n"
                                        "  initial begin\n"
                                        "    $assertcontrol(4, 1, 7);\n"
                                        "    assert(0);\n"
                                        "  end\n"
                                        "endmodule\n"),
            1);
  EXPECT_EQ(RunAndGetAssertionFailCount("module t;\n"
                                        "  initial begin\n"
                                        "    $assertcontrol(4, 255, 7);\n"
                                        "    assert(0);\n"
                                        "  end\n"
                                        "endmodule\n"),
            0);
}

TEST(AssertControlSim, DirectiveTypeMaskExcludesAssertDirective) {
  EXPECT_EQ(RunAndGetAssertionFailCount("module t;\n"
                                        "  initial begin\n"
                                        "    $assertcontrol(4, 255, 2);\n"
                                        "    assert(0);\n"
                                        "  end\n"
                                        "endmodule\n"),
            1);
}

TEST(AssertControlSim, AssertKillStopsImmediateAssertionChecking) {
  EXPECT_EQ(RunAndGetAssertionFailCount("module t;\n"
                                        "  initial begin\n"
                                        "    $assertkill;\n"
                                        "    assert(0);\n"
                                        "  end\n"
                                        "endmodule\n"),
            0);
}

TEST(AssertControlSim, FailOffSuppressesDefaultErrorButStillCounts) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    $assertfailoff;\n"
      "    assert(0);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.AssertionFailCount(), 1);
  EXPECT_NE(f.ctx.LastSeverity(), "ERROR");

  SimFixture g;
  auto* design2 = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    $assertfailoff;\n"
      "    $assertfailon;\n"
      "    assert(0);\n"
      "  end\n"
      "endmodule\n",
      g);
  ASSERT_NE(design2, nullptr);
  Lowerer lowerer2(g.ctx, g.arena, g.diag);
  lowerer2.Lower(design2);
  g.scheduler.Run();
  EXPECT_EQ(g.ctx.AssertionFailCount(), 1);
  EXPECT_EQ(g.ctx.LastSeverity(), "ERROR");
}

TEST(AssertControlSim, AScopeListSelectsTheAssertionsOfItsScopes) {
  EXPECT_EQ(RunAndGetAssertionFailCount("module m;\n"
                                        "endmodule\n"
                                        "module t;\n"
                                        "  m u();\n"
                                        "  initial begin\n"
                                        "    $assertoff(0, t.u);\n"
                                        "    assert(0);\n"
                                        "    $assertoff(0, t);\n"
                                        "    assert(0);\n"
                                        "  end\n"
                                        "endmodule\n"),
            1);
}

TEST(AssertControlSim, ControlTypeFromLocalparam) {
  EXPECT_EQ(RunAndGetAssertionFailCount("module t;\n"
                                        "  localparam int OFF = 4;\n"
                                        "  initial begin\n"
                                        "    $assertcontrol(OFF);\n"
                                        "    assert(0);\n"
                                        "  end\n"
                                        "endmodule\n"),
            0);
}

TEST(AssertControlSim, ControlAndAssertionTypeFromParameters) {
  EXPECT_EQ(RunAndGetAssertionFailCount("module t;\n"
                                        "  parameter int OFF = 4;\n"
                                        "  parameter int ALL = 255;\n"
                                        "  initial begin\n"
                                        "    $assertcontrol(OFF, ALL, 7);\n"
                                        "    assert(0);\n"
                                        "  end\n"
                                        "endmodule\n"),
            0);
}

TEST(AssertControlSim, AssertOffStopsImmediateAssume) {
  EXPECT_EQ(RunAndGetAssertionFailCount("module t;\n"
                                        "  initial begin\n"
                                        "    $assertoff;\n"
                                        "    assume(0);\n"
                                        "  end\n"
                                        "endmodule\n"),
            0);
}

TEST(AssertControlSim, AssertOffStopsDeferredObservedAssertion) {
  EXPECT_EQ(RunAndGetAssertionFailCount("module t;\n"
                                        "  initial begin\n"
                                        "    $assertoff;\n"
                                        "    assert #0 (0);\n"
                                        "  end\n"
                                        "endmodule\n"),
            0);
}

TEST(AssertControlSim, DirectiveMaskStopsCoverImmediate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    $assertcontrol(4, 255, 2);\n"
      "    cover(1);\n"
      "    cover(1);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.ImmediateCovers().Evaluated(), 0u);
}

TEST(AssertControlSim, AssertKillAbortsAnImplicationInFlight) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0;\n"
      "  initial repeat (20) #5 clk = ~clk;\n"
      "  bit [0:9] av = 10'b0010100000;\n"
      "  bit a, b = 0;\n"
      "  assign a = av[0];\n"
      "  always @(negedge clk) av <= av << 1;\n"
      "  int p = 0, f = 0;\n"
      "  assert property (@(posedge clk) a |=> b) p++; else f++;\n"
      "  initial begin\n"
      "    #32 $assertkill;\n"
      "    #10 $asserton;\n"
      "  end\n"
      "  initial #98 $display(\"p=%0d f=%0d\", p, f);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "p=7 f=1\n");
}

TEST(AssertControlSim, AssertKillAbortsASequenceInFlight) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0;\n"
      "  initial repeat (20) #5 clk = ~clk;\n"
      "  bit b = 0;\n"
      "  int f = 0;\n"
      "  assert property (@(posedge clk) 1 ##1 b) else f++;\n"
      "  initial begin\n"
      "    #32 $assertkill;\n"
      "    #10 $asserton;\n"
      "  end\n"
      "  initial #98 $display(\"f=%0d\", f);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "f=7\n");
}

TEST(AssertControlSim, AssertOffLetsAnImplicationInFlightFinish) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic clk = 0;\n"
                       "  initial repeat (10) #5 clk = ~clk;\n"
                       "  bit a = 1, b = 0;\n"
                       "  assert property (@(posedge clk) a |-> ##2 b)\n"
                       "    else $display(\"fail %0d\", $time);\n"
                       "  initial #6 $assertoff;\n"
                       "endmodule\n",
                       f),
            "fail 25\n");
}

TEST(AssertControlSim, AssertOffLetsASequenceInFlightFinish) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic clk = 0;\n"
                       "  initial repeat (10) #5 clk = ~clk;\n"
                       "  bit b = 0;\n"
                       "  assert property (@(posedge clk) 1 ##2 b)\n"
                       "    else $display(\"fail %0d\", $time);\n"
                       "  initial #6 $assertoff;\n"
                       "endmodule\n",
                       f),
            "fail 25\n");
}

TEST(AssertControlSim, AssertKillAbortsAFutureSampledValueAttemptInFlight) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0;\n"
      "  initial repeat (20) #5 clk = ~clk;\n"
      "  global clocking @(posedge clk); endclocking\n"
      "  bit b = 0;\n"
      "  int f = 0;\n"
      "  assert property (@(posedge clk) $rising_gclk(b)) else f++;\n"
      "  initial begin\n"
      "    #7 $assertkill;\n"
      "    #5 $asserton;\n"
      "  end\n"
      "  initial #98 $display(\"f=%0d\", f);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "f=8\n");
}

TEST(AssertControlSim, FailOffAndPassOffStopTheActionBlocks) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  initial begin\n"
                       "    $assertcontrol(9);\n"
                       "    assert (1) $display(\"pass1\"); "
                       "else $display(\"fail1\");\n"
                       "    assert (0) $display(\"pass1b\"); "
                       "else $display(\"fail1b\");\n"
                       "    $assertcontrol(8);\n"
                       "    $assertcontrol(7);\n"
                       "    assert (1) $display(\"pass2\"); "
                       "else $display(\"fail2\");\n"
                       "    assert (0) $display(\"pass2b\"); "
                       "else $display(\"fail2b\");\n"
                       "    $assertcontrol(6);\n"
                       "    assert (1) $display(\"pass3\"); "
                       "else $display(\"fail3\");\n"
                       "    assert (0) $display(\"pass4\"); "
                       "else $display(\"fail4\");\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "pass1\nfail2b\npass3\nfail4\n");
}

TEST(AssertControlSim, TheAssertionTypeSelectsTheAssertionsControlled) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic clk = 0;\n"
                       "  logic a = 0;\n"
                       "  always #1 clk = ~clk;\n"
                       "  a1: assert property (@(posedge clk) a) "
                       "else $display(\"cfail %0d\", $time);\n"
                       "  initial begin\n"
                       "    @(negedge clk);\n"
                       "    $assertcontrol(4, 2);\n"
                       "    assert (0) else $display(\"ifail\");\n"
                       "    @(negedge clk);\n"
                       "    $assertcontrol(4, 1);\n"
                       "    @(negedge clk);\n"
                       "    $assertcontrol(3);\n"
                       "    @(negedge clk);\n"
                       "    $finish(0);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "cfail 1\ncfail 3\ncfail 7\n");
}

TEST(AssertControlSim, ANamedAssertionInTheListIsControlledAlone) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic clk = 0;\n"
                       "  logic a = 0;\n"
                       "  always #1 clk = ~clk;\n"
                       "  ax: assert property (@(posedge clk) a) "
                       "else $display(\"xfail %0d\", $time);\n"
                       "  ay: assert property (@(posedge clk) a) "
                       "else $display(\"yfail %0d\", $time);\n"
                       "  initial begin\n"
                       "    $assertoff(0, ay);\n"
                       "    @(negedge clk);\n"
                       "    $assertkill(0, ax);\n"
                       "    @(negedge clk);\n"
                       "    $asserton(0, ax);\n"
                       "    @(negedge clk);\n"
                       "    $asserton(0, ay);\n"
                       "    @(negedge clk);\n"
                       "    $finish(0);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "xfail 1\nxfail 5\nxfail 7\nyfail 7\n");
}

TEST(AssertControlSim, ALockedAssertionIsUnaffectedUntilUnlocked) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic clk = 0;\n"
                       "  logic a = 0;\n"
                       "  always #1 clk = ~clk;\n"
                       "  a1: assert property (@(posedge clk) a) "
                       "else $display(\"a1 %0d\", $time);\n"
                       "  a2: assert property (@(posedge clk) a) "
                       "else $display(\"a2 %0d\", $time);\n"
                       "  initial begin\n"
                       "    $assertcontrol(1, 31, 7, 0, a1);\n"
                       "    $assertoff;\n"
                       "    @(negedge clk);\n"
                       "    $assertcontrol(2, 31, 7, 0, a1);\n"
                       "    $assertoff;\n"
                       "    @(negedge clk);\n"
                       "    $asserton;\n"
                       "    @(negedge clk);\n"
                       "    $finish(0);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "a1 1\na1 5\na2 5\n");
}

}  // namespace
