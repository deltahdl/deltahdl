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

// §16.9.3: $fell returns false when the LSB did not change to 0.
TEST(Assertion, FellFalseWhenNotFalling) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_fell2";
  prop.kind = SvaPropertyKind::kFell;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_fell2", 0);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_fell2"));
  entry->cycle_count = 1;

  EXPECT_EQ(monitor.Evaluate("p_fell2", 0), AssertionResult::kFail);
}

// §16.9.3 ($rose negative form): a falling LSB is not a rise, so $rose returns
// false when the LSB changes from 1 to 0.
TEST(Assertion, RoseFalseWhenLsbFalls) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_rose3";
  prop.kind = SvaPropertyKind::kRose;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_rose3", 1);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_rose3"));
  entry->cycle_count = 1;

  EXPECT_EQ(monitor.Evaluate("p_rose3", 0), AssertionResult::kFail);
}

// §16.9.3 ($rose is LSB-only): $rose watches only the least significant bit. A
// change confined to the higher bits (2'b00 -> 2'b10) does not raise the LSB,
// so $rose is false even though the value changed. This is the distinction from
// $changed, which observes the whole value.
TEST(Assertion, RoseIgnoresHigherBitsWhenLsbUnchanged) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_rose4";
  prop.kind = SvaPropertyKind::kRose;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_rose4", 0);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_rose4"));
  entry->cycle_count = 1;

  EXPECT_EQ(monitor.Evaluate("p_rose4", 2), AssertionResult::kFail);
}

// §16.9.3 ($fell negative form): a rising LSB is not a fall, so $fell returns
// false when the LSB changes from 0 to 1.
TEST(Assertion, FellFalseWhenLsbRises) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_fell3";
  prop.kind = SvaPropertyKind::kFell;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_fell3", 0);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_fell3"));
  entry->cycle_count = 1;

  EXPECT_EQ(monitor.Evaluate("p_fell3", 1), AssertionResult::kFail);
}

// §16.9.3 ($fell is LSB-only): a change confined to the higher bits
// (2'b01 -> 2'b11) leaves the LSB at 1, so $fell is false even though the value
// changed — the counterpart of the $rose LSB-only case.
TEST(Assertion, FellIgnoresHigherBitsWhenLsbUnchanged) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_fell4";
  prop.kind = SvaPropertyKind::kFell;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_fell4", 1);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_fell4"));
  entry->cycle_count = 1;

  EXPECT_EQ(monitor.Evaluate("p_fell4", 3), AssertionResult::kFail);
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

}  // namespace
