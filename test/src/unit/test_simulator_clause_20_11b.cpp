// Non-LRM tests

#include <gtest/gtest.h>
#include <cstdint>
#include <string_view>
#include <vector>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine.h"

using namespace delta;

// =============================================================================
// Test fixture
// =============================================================================
struct SvaFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
  SvaEngine engine;
};

namespace {

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

}  // namespace
