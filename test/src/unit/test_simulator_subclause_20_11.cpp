#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/sva_engine.h"
#include "simulator/variable.h"

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

// §20.11: Lock (control_type 1) prevents any status change until Unlock
// (control_type 2); while locked, $assertcontrol does not affect the assertion.
TEST(SvaEngine, LockPreventsStatusChangeUntilUnlock) {
  AssertionControl ctrl;
  ctrl.Lock("inst1");
  ctrl.SetOff("inst1");
  EXPECT_TRUE(ctrl.IsEnabled("inst1"));  // Off was ignored while locked
  ctrl.Unlock("inst1");
  ctrl.SetOff("inst1");
  EXPECT_FALSE(ctrl.IsEnabled("inst1"));
}

// §20.11: Unlock is the only control that reaches a locked assertion.
TEST(SvaEngine, UnlockReachesLockedAssertion) {
  AssertionControl ctrl;
  ctrl.ApplyControl(static_cast<int>(AssertControlType::kLock), "inst1");
  ctrl.ApplyControl(static_cast<int>(AssertControlType::kOff), "inst1");
  EXPECT_TRUE(ctrl.IsEnabled("inst1"));
  ctrl.ApplyControl(static_cast<int>(AssertControlType::kUnlock), "inst1");
  EXPECT_FALSE(ctrl.IsLocked("inst1"));
}

// §20.11: ApplyControl dispatches Off (4) and On (3) by integer control_type.
TEST(SvaEngine, ApplyControlOffOnByControlType) {
  AssertionControl ctrl;
  ctrl.ApplyControl(static_cast<int>(AssertControlType::kOff), "inst1");
  EXPECT_FALSE(ctrl.IsEnabled("inst1"));
  ctrl.ApplyControl(static_cast<int>(AssertControlType::kOn), "inst1");
  EXPECT_TRUE(ctrl.IsEnabled("inst1"));
}

// §20.11: VacuousOff (11) stops the pass action on vacuous success while
// leaving nonvacuous success enabled; PassOn (6) re-enables both.
TEST(SvaEngine, VacuousOffDisablesOnlyVacuousPass) {
  AssertionControl ctrl;
  ctrl.SetVacuousOff("inst1");
  EXPECT_FALSE(ctrl.IsVacuousPassEnabled("inst1"));
  EXPECT_TRUE(ctrl.IsNonvacuousPassEnabled("inst1"));
  ctrl.SetPassOn("inst1");
  EXPECT_TRUE(ctrl.IsVacuousPassEnabled("inst1"));
}

// §20.11: PassOff (7) stops both kinds of pass action; NonvacuousOn (10)
// re-enables only the nonvacuous pass action.
TEST(SvaEngine, NonvacuousOnReenablesNonvacuousPassOnly) {
  AssertionControl ctrl;
  ctrl.SetPassOff("inst1");
  EXPECT_FALSE(ctrl.IsNonvacuousPassEnabled("inst1"));
  ctrl.SetNonvacuousOn("inst1");
  EXPECT_TRUE(ctrl.IsNonvacuousPassEnabled("inst1"));
  EXPECT_FALSE(ctrl.IsVacuousPassEnabled("inst1"));
}

// §20.11: the action controls (control_type 6 through 11) do not affect the
// statistics counters, while the status controls (1 through 5) do.
TEST(SvaEngine, OnlyStatusControlsAffectStatistics) {
  EXPECT_TRUE(
      ControlTypeAffectsStatistics(static_cast<int>(AssertControlType::kKill)));
  EXPECT_FALSE(ControlTypeAffectsStatistics(
      static_cast<int>(AssertControlType::kPassOn)));
  EXPECT_FALSE(ControlTypeAffectsStatistics(
      static_cast<int>(AssertControlType::kVacuousOff)));
}

// §20.11: $assertoff is equivalent to $assertcontrol(4, 15, 7, ...).
TEST(SvaEngine, AssertOffEquivalentToControl) {
  AssertControlInvocation inv;
  ASSERT_TRUE(EquivalentAssertControlForTask("$assertoff", inv));
  EXPECT_EQ(inv.control_type, static_cast<uint32_t>(AssertControlType::kOff));
  EXPECT_EQ(inv.assertion_type, 15u);
  EXPECT_EQ(inv.directive_type, 7u);
}

// §20.11: the action control tasks expand with assertion_type 31; e.g.
// $assertfailoff is $assertcontrol(9, 31, 7, ...).
TEST(SvaEngine, AssertFailOffEquivalentToControl) {
  AssertControlInvocation inv;
  ASSERT_TRUE(EquivalentAssertControlForTask("$assertfailoff", inv));
  EXPECT_EQ(inv.control_type,
            static_cast<uint32_t>(AssertControlType::kFailOff));
  EXPECT_EQ(inv.assertion_type, 31u);
}

// §20.11: a name that is not a convenience control task does not expand.
TEST(SvaEngine, NonControlTaskHasNoEquivalent) {
  AssertControlInvocation inv;
  EXPECT_FALSE(EquivalentAssertControlForTask("$display", inv));
}

// §20.11: assertion_type defaults to 255 and directive_type defaults to 7 when
// the arguments are not specified.
TEST(SvaEngine, ControlArgumentDefaults) {
  EXPECT_EQ(kAssertionTypeDefault, 255u);
  EXPECT_EQ(kDirectiveTypeDefault, 7u);
}

// §20.11: ApplyControl dispatches PassOff (7) to disabling the pass action and
// PassOn (6) to re-enabling it, keyed by integer control_type.
TEST(SvaEngine, ApplyControlPassOffPassOnByControlType) {
  AssertionControl ctrl;
  ctrl.ApplyControl(static_cast<int>(AssertControlType::kPassOff), "inst1");
  EXPECT_FALSE(ctrl.IsPassEnabled("inst1"));
  ctrl.ApplyControl(static_cast<int>(AssertControlType::kPassOn), "inst1");
  EXPECT_TRUE(ctrl.IsPassEnabled("inst1"));
}

// §20.11: ApplyControl dispatches FailOff (9) to disabling the fail action and
// FailOn (8) to re-enabling it.
TEST(SvaEngine, ApplyControlFailOffFailOnByControlType) {
  AssertionControl ctrl;
  ctrl.ApplyControl(static_cast<int>(AssertControlType::kFailOff), "inst1");
  EXPECT_FALSE(ctrl.IsFailEnabled("inst1"));
  ctrl.ApplyControl(static_cast<int>(AssertControlType::kFailOn), "inst1");
  EXPECT_TRUE(ctrl.IsFailEnabled("inst1"));
}

// §20.11: ApplyControl dispatches VacuousOff (11) to disabling only the vacuous
// pass action and NonvacuousOn (10) to enabling the nonvacuous pass action.
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

// §20.11: ApplyControl dispatches Kill (5), which disables the assertion and
// records that it was killed.
TEST(SvaEngine, ApplyControlKillByControlType) {
  AssertionControl ctrl;
  ctrl.ApplyControl(static_cast<int>(AssertControlType::kKill), "inst1");
  EXPECT_FALSE(ctrl.IsEnabled("inst1"));
  EXPECT_TRUE(ctrl.WasKilled("inst1"));
}

// §20.11: the $asserton/$assertoff/$assertkill tasks expand with assertion_type
// 15 and directive_type 7; their control_types are On (3), Off (4), Kill (5).
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

// §20.11: the action control tasks expand with assertion_type 31; this covers
// the pass/fail/vacuity tasks not exercised elsewhere.
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

// §20.11: while an assertion is locked, no control other than Unlock affects it
// — a pass action control is ignored until the lock is removed.
TEST(SvaEngine, LockAlsoBlocksActionControls) {
  AssertionControl ctrl;
  ctrl.Lock("inst1");
  ctrl.SetPassOff("inst1");
  EXPECT_TRUE(ctrl.IsPassEnabled("inst1"));  // PassOff ignored while locked
  ctrl.SetFailOff("inst1");
  EXPECT_TRUE(ctrl.IsFailEnabled("inst1"));  // FailOff ignored while locked
  ctrl.Unlock("inst1");
  ctrl.SetPassOff("inst1");
  EXPECT_FALSE(ctrl.IsPassEnabled("inst1"));
}

// §20.11: the status controls (1 through 5) affect statistics counters; the
// boundary is at control_type 5/6. Lock (1) and On (3) affect them.
TEST(SvaEngine, StatusControlsBelowSixAffectStatistics) {
  EXPECT_TRUE(
      ControlTypeAffectsStatistics(static_cast<int>(AssertControlType::kLock)));
  EXPECT_TRUE(
      ControlTypeAffectsStatistics(static_cast<int>(AssertControlType::kOn)));
  EXPECT_FALSE(ControlTypeAffectsStatistics(
      static_cast<int>(AssertControlType::kPassOff)));
}

// §20.11: an assertion_type mask selects assertion kinds by OR-ing Table 20-6
// values; mask 3 (Concurrent|SimpleImmediate) affects those two kinds only.
TEST(SvaEngine, AssertionTypeMaskSelectsKinds) {
  uint32_t mask = static_cast<uint32_t>(AssertionTypeBit::kConcurrent) |
                  static_cast<uint32_t>(AssertionTypeBit::kSimpleImmediate);
  EXPECT_TRUE(ControlAffectsAssertionType(mask, AssertionTypeBit::kConcurrent));
  EXPECT_TRUE(
      ControlAffectsAssertionType(mask, AssertionTypeBit::kSimpleImmediate));
  EXPECT_FALSE(ControlAffectsAssertionType(
      mask, AssertionTypeBit::kObservedDeferredImmediate));
}

// §20.11: the default assertion_type (255) affects every Table 20-6 kind,
// including unique and priority types.
TEST(SvaEngine, DefaultAssertionTypeAffectsAllKinds) {
  EXPECT_TRUE(ControlAffectsAssertionType(kAssertionTypeDefault,
                                          AssertionTypeBit::kConcurrent));
  EXPECT_TRUE(ControlAffectsAssertionType(kAssertionTypeDefault,
                                          AssertionTypeBit::kExpect));
  EXPECT_TRUE(ControlAffectsAssertionType(kAssertionTypeDefault,
                                          AssertionTypeBit::kPriority));
}

// §20.11: a directive_type mask selects directive kinds; mask 3 (Assert|Cover)
// affects assert and cover but not assume directives.
TEST(SvaEngine, DirectiveTypeMaskSelectsDirectives) {
  uint32_t mask = static_cast<uint32_t>(DirectiveTypeBit::kAssert) |
                  static_cast<uint32_t>(DirectiveTypeBit::kCover);
  EXPECT_TRUE(ControlAffectsDirectiveType(mask, DirectiveTypeBit::kAssert));
  EXPECT_TRUE(ControlAffectsDirectiveType(mask, DirectiveTypeBit::kCover));
  EXPECT_FALSE(ControlAffectsDirectiveType(mask, DirectiveTypeBit::kAssume));
}

// §20.11: the default directive_type (7) affects all three directive kinds.
TEST(SvaEngine, DefaultDirectiveTypeAffectsAllDirectives) {
  EXPECT_TRUE(ControlAffectsDirectiveType(kDirectiveTypeDefault,
                                          DirectiveTypeBit::kAssert));
  EXPECT_TRUE(ControlAffectsDirectiveType(kDirectiveTypeDefault,
                                          DirectiveTypeBit::kCover));
  EXPECT_TRUE(ControlAffectsDirectiveType(kDirectiveTypeDefault,
                                          DirectiveTypeBit::kAssume));
}

// The full-pipeline tests below drive an assertion control system task from
// real source and observe its effect on a real immediate assertion (§16.3),
// which is how §20.11's control_type/assertion_type/directive_type semantics
// are meant to be applied. Each builds the assertion and the control task from
// source, then parses, elaborates, lowers, and runs the design.
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

// §20.11: $assertoff (Off) shall stop the checking of the immediate assertions
// it selects, so a failing immediate assert reports no violation.
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

// §20.11: $asserton (On) shall re-enable checking after an $assertoff, so only
// the assertion evaluated while checking is on reports its failure.
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

// §20.11: $assertcontrol dispatches by integer control_type; Off (4) stops
// checking and On (3) re-enables it, exactly as the convenience tasks do.
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

// §20.11: the assertion_type argument selects which assertion kinds a control
// affects. An Off whose mask is Concurrent-only (bit 1) does not include simple
// immediate (bit 2), so a simple immediate assert keeps checking and still
// reports its failure -- the mask is honored end to end.
TEST(AssertControlSim, AssertionTypeMaskExcludesSimpleImmediate) {
  EXPECT_EQ(RunAndGetAssertionFailCount("module t;\n"
                                        "  initial begin\n"
                                        "    $assertcontrol(4, 1, 7);\n"
                                        "    assert(0);\n"
                                        "  end\n"
                                        "endmodule\n"),
            1);
  // With the default mask (255) the same Off does stop the checking.
  EXPECT_EQ(RunAndGetAssertionFailCount("module t;\n"
                                        "  initial begin\n"
                                        "    $assertcontrol(4, 255, 7);\n"
                                        "    assert(0);\n"
                                        "  end\n"
                                        "endmodule\n"),
            0);
}

// §20.11: the directive_type argument likewise selects directive kinds. An Off
// whose directive mask is Cover-only (bit 2) does not include assert (bit 1),
// so an assert directive keeps checking.
TEST(AssertControlSim, DirectiveTypeMaskExcludesAssertDirective) {
  EXPECT_EQ(RunAndGetAssertionFailCount("module t;\n"
                                        "  initial begin\n"
                                        "    $assertcontrol(4, 255, 2);\n"
                                        "    assert(0);\n"
                                        "  end\n"
                                        "endmodule\n"),
            1);
}

// §20.11: Kill (5), like Off, stops the checking of the selected assertions.
TEST(AssertControlSim, AssertKillStopsImmediateAssertionChecking) {
  EXPECT_EQ(RunAndGetAssertionFailCount("module t;\n"
                                        "  initial begin\n"
                                        "    $assertkill;\n"
                                        "    assert(0);\n"
                                        "  end\n"
                                        "endmodule\n"),
            0);
}

// §20.11: $assertfailoff (FailOff) stops the fail action, including the default
// $error, but the action controls do not affect the statistics counters -- so
// the failure is still counted while no ERROR is reported. $assertfailon
// restores the report.
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

// §20.11: a control that names a scope list targets those scopes rather than
// the whole design; immediate assertions are not registered by hierarchical
// name, so such a task leaves them checking (it does not turn off the whole
// design).
TEST(AssertControlSim, ScopedOffDoesNotStopWholeDesignChecking) {
  EXPECT_EQ(RunAndGetAssertionFailCount("module t;\n"
                                        "  initial begin\n"
                                        "    $assertoff(0, t);\n"
                                        "    assert(0);\n"
                                        "  end\n"
                                        "endmodule\n"),
            1);
}

// §20.11: control_type shall be an integer expression, not necessarily a
// literal. A localparam supplies the control_type here, which resolves to Off;
// the failing assert is then not checked.
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

// §20.11: control_type and assertion_type are integer expressions; parameters
// supply both here (Off with the default-all mask), so the failing assert is
// not checked -- the same effect as the literal form, via the parameter path.
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

// §20.11: the default directive_type (7) selects assume directives too, so Off
// stops the checking of an immediate assume (which is otherwise checked like an
// assert, §16.3).
TEST(AssertControlSim, AssertOffStopsImmediateAssume) {
  EXPECT_EQ(RunAndGetAssertionFailCount("module t;\n"
                                        "  initial begin\n"
                                        "    $assertoff;\n"
                                        "    assume(0);\n"
                                        "  end\n"
                                        "endmodule\n"),
            0);
}

// §20.11: the assertion_type mask selects the deferred immediate kinds as well.
// $assertoff (assertion_type 15) includes observed deferred immediate, so a
// failing `assert #0` is not checked and records no failure.
TEST(AssertControlSim, AssertOffStopsDeferredObservedAssertion) {
  EXPECT_EQ(RunAndGetAssertionFailCount("module t;\n"
                                        "  initial begin\n"
                                        "    $assertoff;\n"
                                        "    assert #0 (0);\n"
                                        "  end\n"
                                        "endmodule\n"),
            0);
}

// §20.11: the directive_type mask selects cover directives. An Off whose
// directive mask is Cover (bit 2) stops the checking of an immediate cover, so
// the cover records no evaluation. Built from real source and driven end to
// end.
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
  EXPECT_EQ(f.ctx.CoverEvalCount(), 0);
}

}  // namespace
