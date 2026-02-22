// §16.12.9: Followed-by property

#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/sva_engine.h"

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

TEST(SvaEngine, PropertyAnd) {
  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kPass, PropertyResult::kPass),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kPass, PropertyResult::kFail),
            PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kFail, PropertyResult::kPass),
            PropertyResult::kFail);
}

}  // namespace
