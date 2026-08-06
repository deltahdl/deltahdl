#include <gtest/gtest.h>

#include <algorithm>
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

TEST(SvaEngine, SequenceOperatorOr) {
  EXPECT_TRUE(EvalSequenceOr(true, false));
  EXPECT_TRUE(EvalSequenceOr(false, true));
  EXPECT_TRUE(EvalSequenceOr(true, true));
  EXPECT_FALSE(EvalSequenceOr(false, false));
}

// §16.9.7: the match set of `a or b` is the union of the two operands' match
// sets, with each composite match ending where its originating operand match
// ends. This reproduces Figure 16-11 for `(te1 ##[1:5] te2) or (te3 ##2 te4 ##2
// te5)`: the first operand matches at ticks 9, 10, 11, 12, and 13, and the
// second matches at tick 12. The composite therefore has one match at each of
// ticks 9, 10, 11, and 13 and two matches at tick 12 — operand matches are not
// merged, so the coincident tick appears twice.
TEST(SvaEngine, SequenceOrIsUnionOfOperandMatches) {
  auto u = EvalSequenceOrMatches({9, 10, 11, 12, 13}, {12});
  EXPECT_TRUE(u.matched);
  std::vector<uint32_t> expected{9, 10, 11, 12, 13, 12};
  EXPECT_EQ(u.end_times, expected);
  // The defining feature of the figure: tick 12 carries two composite matches.
  EXPECT_EQ(std::count(u.end_times.begin(), u.end_times.end(), 12u), 2);
}

// §16.9.7: a match of either operand alone is a match of the composite, ending
// at that operand's own end time.
TEST(SvaEngine, SequenceOrMatchesWhenOnlyOneOperandMatches) {
  auto only_a = EvalSequenceOrMatches({7}, {});
  EXPECT_TRUE(only_a.matched);
  EXPECT_EQ(only_a.end_times, std::vector<uint32_t>{7});

  auto only_b = EvalSequenceOrMatches({}, {4});
  EXPECT_TRUE(only_b.matched);
  EXPECT_EQ(only_b.end_times, std::vector<uint32_t>{4});
}

// §16.9.7: with neither operand matching, the composite has no match.
TEST(SvaEngine, SequenceOrHasNoMatchWhenNeitherOperandMatches) {
  auto u = EvalSequenceOrMatches({}, {});
  EXPECT_FALSE(u.matched);
  EXPECT_TRUE(u.end_times.empty());
}

}  // namespace
