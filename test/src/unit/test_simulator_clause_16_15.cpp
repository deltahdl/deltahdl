#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine.h"

using namespace delta;

struct SvaFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
  SvaEngine engine;
};

namespace {

TEST(SvaEngine, DisableIffTrue) {
  PropertyResult result = EvalWithDisableIff(true, PropertyResult::kFail);
  EXPECT_EQ(result, PropertyResult::kVacuousPass);
}

TEST(SvaEngine, DisableIffFalse) {
  PropertyResult result = EvalWithDisableIff(false, PropertyResult::kFail);
  EXPECT_EQ(result, PropertyResult::kFail);
}

TEST(SvaEngine, DisableIffFalsePass) {
  PropertyResult result = EvalWithDisableIff(false, PropertyResult::kPass);
  EXPECT_EQ(result, PropertyResult::kPass);
}

}
