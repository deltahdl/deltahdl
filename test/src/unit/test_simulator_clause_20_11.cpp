// §20.11: Assertion control system tasks

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"

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

// =============================================================================
// AssertionControl: $assertoff/$asserton/$assertkill (section 16.13)
// =============================================================================
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

TEST(SvaEngine, AssertonReenablesInstance) {
  AssertionControl ctrl;
  ctrl.SetOff("inst1");
  EXPECT_FALSE(ctrl.IsEnabled("inst1"));
  ctrl.SetOn("inst1");
  EXPECT_TRUE(ctrl.IsEnabled("inst1"));
}

TEST(SvaEngine, AssertkillKillsAndDisables) {
  AssertionControl ctrl;
  ctrl.Kill("inst1");
  EXPECT_FALSE(ctrl.IsEnabled("inst1"));
  EXPECT_TRUE(ctrl.WasKilled("inst1"));
}

// =============================================================================
// $assertcontrol, $assertpassoff, $assertfailon (section 16.13)
// =============================================================================
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

}  // namespace
