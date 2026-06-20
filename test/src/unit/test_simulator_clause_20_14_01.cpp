#include <set>
#include <vector>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// Draws a stream of `n` numbers from $random, supplying `seed` on the first
// call (which selects the stream) and then continuing with the seedless form so
// each subsequent draw advances the same stream — the usual $random usage.
std::vector<int32_t> RandomStream(SimFixture& f, uint32_t seed, int n) {
  std::vector<int32_t> out;
  auto* seeded = MkSysCall(f.arena, "$random", {MkInt(f.arena, seed)});
  out.push_back(
      static_cast<int32_t>(EvalExpr(seeded, f.ctx, f.arena).ToUint64()));
  for (int i = 1; i < n; ++i) {
    auto* call = MkSysCall(f.arena, "$random", {});
    out.push_back(
        static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64()));
  }
  return out;
}

// §20.14.1: $random returns a new 32-bit number each time it is called.
TEST(RandomFunction, Returns32BitValue) {
  SimFixture f;
  auto* call = MkSysCall(f.arena, "$random", {});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

// §20.14.1: supplying a seed still yields a fresh 32-bit draw — the seeded form
// reseeds the stream and returns a new 32-bit number through the same code
// path, exercising the seed branch rather than echoing the seed.
TEST(RandomFunction, SeededCallReturns32BitValue) {
  SimFixture f;
  auto* call = MkSysCall(f.arena, "$random", {MkInt(f.arena, 99u)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

// §20.14.1: a new number is produced on each call, so consecutive draws from
// one stream are not pinned to a single value.
TEST(RandomFunction, AdvancesAcrossConsecutiveCalls) {
  SimFixture f;
  std::set<int32_t> seen;
  for (int i = 0; i < 8; ++i) {
    auto* call = MkSysCall(f.arena, "$random", {});
    seen.insert(
        static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64()));
  }
  EXPECT_GT(seen.size(), 1u);
}

// §20.14.1: the random number is a signed integer; it can be positive or
// negative. Over a run of draws both signs appear, which only holds if the
// 32-bit result is interpreted as signed.
TEST(RandomFunction, ProducesPositiveAndNegativeValues) {
  SimFixture f;
  bool saw_negative = false;
  bool saw_positive = false;
  for (int i = 0; i < 200 && !(saw_negative && saw_positive); ++i) {
    auto* call = MkSysCall(f.arena, "$random", {});
    int32_t v = static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64());
    if (v < 0) saw_negative = true;
    if (v > 0) saw_positive = true;
  }
  EXPECT_TRUE(saw_negative);
  EXPECT_TRUE(saw_positive);
}

// §20.14.1: the seed argument controls the numbers $random returns, so
// different seeds generate different random streams.
TEST(RandomFunction, DifferentSeedsGiveDifferentStreams) {
  SimFixture f;
  auto stream_a = RandomStream(f, 1, 6);
  auto stream_b = RandomStream(f, 2, 6);
  EXPECT_NE(stream_a, stream_b);
}

// §20.14.1 (corollary): seeding controls the stream deterministically, so the
// same seed replays the identical sequence.
TEST(RandomFunction, SameSeedReplaysStream) {
  SimFixture f;
  auto first = RandomStream(f, 12345, 6);
  auto second = RandomStream(f, 12345, 6);
  EXPECT_EQ(first, second);
}

}  // namespace
