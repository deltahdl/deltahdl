// §non-lrm:eval_advanced

#include <gtest/gtest.h>

#include <cstring>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulation/adv_sim.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"  // StructTypeInfo, StructFieldInfo

using namespace delta;

// Shared fixture for advanced expression evaluation tests (§11 phases 22+).
struct EvalAdvFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

namespace {

// =============================================================================
// TwoStateDetector
// =============================================================================
TEST(AdvSim, TwoStateDetectorKnown2State) {
  Arena arena;
  auto vec = MakeLogic4VecVal(arena, 8, 0x42);
  EXPECT_TRUE(TwoStateDetector::Is2State(vec));
}

TEST(AdvSim, TwoStateDetectorWith4StateValue) {
  Arena arena;
  auto vec = MakeLogic4Vec(arena, 8);
  // Set bval to non-zero to indicate X/Z.
  vec.words[0].bval = 0x01;
  EXPECT_FALSE(TwoStateDetector::Is2State(vec));
}

TEST(AdvSim, TwoStateDetectorZeroWidth) {
  Logic4Vec empty;
  empty.width = 0;
  empty.nwords = 0;
  empty.words = nullptr;
  EXPECT_TRUE(TwoStateDetector::Is2State(empty));
}

TEST(AdvSim, EventCoalescerKeepsDistinctTargets) {
  EventCoalescer coalescer;
  coalescer.Add(1, 10);
  coalescer.Add(2, 20);
  coalescer.Add(3, 30);
  auto entries = coalescer.Drain();
  EXPECT_EQ(entries.size(), 3u);
}

}  // namespace
