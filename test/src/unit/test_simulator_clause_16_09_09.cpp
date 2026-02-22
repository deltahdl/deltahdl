// §16.9.9: Conditions over sequences

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

// =============================================================================
// Sequence throughout (section 16.9.9)
// =============================================================================
TEST(SvaEngine, SequenceThroughout) {
  // expr must hold throughout the entire sequence.
  std::vector<uint64_t> values = {1, 1, 1, 1};
  auto check = [](uint64_t v) { return v == 1; };
  EXPECT_TRUE(EvalThroughout(check, values));

  values = {1, 1, 0, 1};
  EXPECT_FALSE(EvalThroughout(check, values));
}

TEST(SvaEngine, SequenceThroughoutEmpty) {
  std::vector<uint64_t> values;
  auto check = [](uint64_t v) { return v == 1; };
  EXPECT_TRUE(EvalThroughout(check, values));
}

}  // namespace
