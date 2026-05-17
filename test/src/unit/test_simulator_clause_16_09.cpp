#include <gtest/gtest.h>

#include <cstdint>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_simulator.h"
#include "simulator/assertion.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine.h"

using namespace delta;

namespace {

TEST(Assertion, RoseDetection) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_rose";
  prop.kind = SvaPropertyKind::kRose;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  auto r0 = monitor.Evaluate("p_rose", 0);
  EXPECT_EQ(r0, AssertionResult::kVacuousPass);

  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_rose"));
  ASSERT_NE(entry, nullptr);
  entry->cycle_count = 1;

  auto r1 = monitor.Evaluate("p_rose", 1);
  EXPECT_EQ(r1, AssertionResult::kPass);

  entry->cycle_count = 2;

  auto r2 = monitor.Evaluate("p_rose", 1);
  EXPECT_EQ(r2, AssertionResult::kFail);
}

TEST(Assertion, FellDetection) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_fell";
  prop.kind = SvaPropertyKind::kFell;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_fell", 1);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_fell"));
  entry->cycle_count = 1;

  auto r1 = monitor.Evaluate("p_fell", 0);
  EXPECT_EQ(r1, AssertionResult::kPass);

  entry->cycle_count = 2;

  auto r2 = monitor.Evaluate("p_fell", 0);
  EXPECT_EQ(r2, AssertionResult::kFail);
}

TEST(Assertion, StableDetection) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_stable";
  prop.kind = SvaPropertyKind::kStable;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_stable", 42);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_stable"));
  entry->cycle_count = 1;

  auto r1 = monitor.Evaluate("p_stable", 42);
  EXPECT_EQ(r1, AssertionResult::kPass);

  entry->cycle_count = 2;
  auto r2 = monitor.Evaluate("p_stable", 99);
  EXPECT_EQ(r2, AssertionResult::kFail);
}

struct SvaFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
  SvaEngine engine;
};

TEST(SvaEngine, SequenceAttemptDefaultState) {
  SequenceAttempt sa;
  EXPECT_EQ(sa.position, 0u);
  EXPECT_EQ(sa.delay_remaining, 0u);
  EXPECT_EQ(sa.match_count, 0u);
  EXPECT_FALSE(sa.completed);
  EXPECT_FALSE(sa.failed);
}

TEST(SvaEngine, SequenceAttemptDelayCountdown) {
  SequenceAttempt sa;
  sa.delay_remaining = 3;
  AdvanceSequence(sa);
  EXPECT_EQ(sa.delay_remaining, 2u);
  EXPECT_FALSE(sa.completed);
  AdvanceSequence(sa);
  EXPECT_EQ(sa.delay_remaining, 1u);
  AdvanceSequence(sa);
  EXPECT_EQ(sa.delay_remaining, 0u);
}

}
