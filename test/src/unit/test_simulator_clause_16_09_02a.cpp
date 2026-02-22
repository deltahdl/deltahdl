// §16.9.2: Repetition in sequences

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulation/assertion.h"
#include "simulation/sim_context.h"
#include <cstdint>
#include <gtest/gtest.h>

using namespace delta;

namespace {

TEST(Assertion, RoseDetection) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_rose";
  prop.kind = SvaPropertyKind::kRose;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  // First evaluation: cycle_count==0, vacuous pass (initializes prev).
  auto r0 = monitor.Evaluate("p_rose", 0);
  EXPECT_EQ(r0, AssertionResult::kVacuousPass);

  // Simulate one tick to advance cycle count.
  // We need a SimContext, but Tick just increments cycle_count.
  // Use a minimal approach: manually increment via a second Evaluate.
  // Actually, we need to call Tick. Let's hack around it by
  // constructing a dummy approach. For the test we'll directly
  // modify the entry cycle count by calling Evaluate after AddProperty.
  // The first Evaluate set prev_value=0, cycle_count was 0.
  // Now "tick" it:
  auto *entry = const_cast<AssertionEntry *>(monitor.FindEntry("p_rose"));
  ASSERT_NE(entry, nullptr);
  entry->cycle_count = 1;

  // 0 -> 1 is a rising edge.
  auto r1 = monitor.Evaluate("p_rose", 1);
  EXPECT_EQ(r1, AssertionResult::kPass);

  entry->cycle_count = 2;
  // 1 -> 1 is NOT a rising edge.
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

  // Initialize: prev_value = 1.
  monitor.Evaluate("p_fell", 1);
  auto *entry = const_cast<AssertionEntry *>(monitor.FindEntry("p_fell"));
  entry->cycle_count = 1;

  // 1 -> 0 is a falling edge.
  auto r1 = monitor.Evaluate("p_fell", 0);
  EXPECT_EQ(r1, AssertionResult::kPass);

  entry->cycle_count = 2;
  // 0 -> 0 is NOT a falling edge.
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
  auto *entry = const_cast<AssertionEntry *>(monitor.FindEntry("p_stable"));
  entry->cycle_count = 1;

  auto r1 = monitor.Evaluate("p_stable", 42);
  EXPECT_EQ(r1, AssertionResult::kPass);

  entry->cycle_count = 2;
  auto r2 = monitor.Evaluate("p_stable", 99);
  EXPECT_EQ(r2, AssertionResult::kFail);
}

// =============================================================================
// §16.9.3: $changed — assertion monitor support
// =============================================================================
TEST(Assertion, ChangedDetected) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_changed";
  prop.kind = SvaPropertyKind::kChanged;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  // Initialize: prev_value = 5.
  monitor.Evaluate("p_changed", 5);
  auto *entry = const_cast<AssertionEntry *>(monitor.FindEntry("p_changed"));
  entry->cycle_count = 1;

  // 5 -> 7 is a change → kPass.
  auto r1 = monitor.Evaluate("p_changed", 7);
  EXPECT_EQ(r1, AssertionResult::kPass);
}

TEST(Assertion, ChangedStable) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_changed2";
  prop.kind = SvaPropertyKind::kChanged;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_changed2", 42);
  auto *entry = const_cast<AssertionEntry *>(monitor.FindEntry("p_changed2"));
  entry->cycle_count = 1;

  // 42 -> 42 is NOT a change → kFail.
  auto r1 = monitor.Evaluate("p_changed2", 42);
  EXPECT_EQ(r1, AssertionResult::kFail);
}

} // namespace
