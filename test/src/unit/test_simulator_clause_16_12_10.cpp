// §16.12.10: Nexttime property

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/sva_engine.h"
#include <cstdint>
#include <gtest/gtest.h>
#include <string_view>
#include <vector>

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

TEST(SvaEngine, PropertyOr) {
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kPass, PropertyResult::kFail),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kFail, PropertyResult::kFail),
            PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kFail, PropertyResult::kPass),
            PropertyResult::kPass);
}

} // namespace
