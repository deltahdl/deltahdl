#include <gtest/gtest.h>

#include <cstdint>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/assertion.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

TEST(Assertion, ChangedDetected) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_changed";
  prop.kind = SvaPropertyKind::kChanged;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_changed", 5);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_changed"));
  entry->cycle_count = 1;

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
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_changed2"));
  entry->cycle_count = 1;

  auto r1 = monitor.Evaluate("p_changed2", 42);
  EXPECT_EQ(r1, AssertionResult::kFail);
}

// §16.9.3: $rose returns true if the LSB of the expression changed to 1.
TEST(Assertion, RoseDetectsLowToHigh) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_rose";
  prop.kind = SvaPropertyKind::kRose;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_rose", 0);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_rose"));
  entry->cycle_count = 1;

  EXPECT_EQ(monitor.Evaluate("p_rose", 1), AssertionResult::kPass);
}

// §16.9.3: $rose returns false when the LSB did not change to 1.
TEST(Assertion, RoseFalseWhenAlreadyHigh) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_rose2";
  prop.kind = SvaPropertyKind::kRose;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_rose2", 1);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_rose2"));
  entry->cycle_count = 1;

  EXPECT_EQ(monitor.Evaluate("p_rose2", 1), AssertionResult::kFail);
}

// §16.9.3: $fell returns true if the LSB of the expression changed to 0.
TEST(Assertion, FellDetectsHighToLow) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_fell";
  prop.kind = SvaPropertyKind::kFell;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_fell", 1);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_fell"));
  entry->cycle_count = 1;

  EXPECT_EQ(monitor.Evaluate("p_fell", 0), AssertionResult::kPass);
}

// §16.9.3: $stable returns true if the value of the expression did not change.
TEST(Assertion, StableTrueWhenUnchanged) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_stable";
  prop.kind = SvaPropertyKind::kStable;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_stable", 9);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_stable"));
  entry->cycle_count = 1;

  EXPECT_EQ(monitor.Evaluate("p_stable", 9), AssertionResult::kPass);
  EXPECT_EQ(monitor.Evaluate("p_stable", 4), AssertionResult::kFail);
}

// §16.9.3: when a value change function is called at or before the first
// clocking event, there is no prior real sample to compare against; the first
// evaluation seeds the sampled value rather than reporting a change.
TEST(Assertion, FirstEvaluationHasNoPriorSample) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_first";
  prop.kind = SvaPropertyKind::kChanged;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  EXPECT_EQ(monitor.Evaluate("p_first", 5), AssertionResult::kVacuousPass);
}

}
