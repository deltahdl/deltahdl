// Non-LRM tests

#include <gtest/gtest.h>
#include <cstdint>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/assertion.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

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

  // 42 -> 42 is NOT a change → kFail.
  auto r1 = monitor.Evaluate("p_changed2", 42);
  EXPECT_EQ(r1, AssertionResult::kFail);
}

}  // namespace
