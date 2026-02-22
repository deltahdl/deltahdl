// §non_lrm

#include <gtest/gtest.h>
#include <cstdint>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulation/assertion.h"
#include "simulation/sim_context.h"

using namespace delta;

namespace {

// =============================================================================
// AssertionMonitor basics
// =============================================================================
TEST(Assertion, AddPropertyAndCount) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_rose";
  prop.kind = SvaPropertyKind::kRose;
  prop.signal_name = "clk";
  monitor.AddProperty(prop);
  EXPECT_EQ(monitor.PropertyCount(), 1u);
}

TEST(Assertion, CustomCheckFunction) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_custom";
  prop.kind = SvaPropertyKind::kCustom;
  prop.signal_name = "sig";
  // Custom: current must be greater than previous.
  prop.custom_check = [](uint64_t cur, uint64_t prev) { return cur > prev; };
  monitor.AddProperty(prop);

  monitor.Evaluate("p_custom", 10);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_custom"));
  entry->cycle_count = 1;

  auto r1 = monitor.Evaluate("p_custom", 20);
  EXPECT_EQ(r1, AssertionResult::kPass);

  entry->cycle_count = 2;
  auto r2 = monitor.Evaluate("p_custom", 5);
  EXPECT_EQ(r2, AssertionResult::kFail);
}

}  // namespace
