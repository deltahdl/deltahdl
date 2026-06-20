#include <set>
#include <vector>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// Draws `n` values from a distribution function whose seed names the variable
// `seed`, evaluating the same call repeatedly. Because the seed is an inout
// argument the call advances it on its own, so each evaluation walks the
// stream.
std::vector<int32_t> DistStream(SimFixture& f, Expr* call, int n) {
  std::vector<int32_t> out;
  for (int i = 0; i < n; ++i) {
    out.push_back(
        static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64()));
  }
  return out;
}

// §20.14.2: every distribution function returns an integer value — a 32-bit
// result through the same path as $random.
TEST(DistributionFunctions, Returns32BitInteger) {
  SimFixture f;
  for (auto name :
       {"$dist_uniform", "$dist_normal", "$dist_exponential", "$dist_poisson",
        "$dist_chi_square", "$dist_t", "$dist_erlang"}) {
    auto* call =
        MkSysCall(f.arena, name,
                  {MkInt(f.arena, 1u), MkInt(f.arena, 5u), MkInt(f.arena, 7u)});
    auto result = EvalExpr(call, f.ctx, f.arena);
    EXPECT_EQ(result.width, 32u) << name;
  }
}

// §20.14.2: $dist_uniform returns numbers uniformly distributed in the interval
// bounded by its start and end arguments, so every draw lands within [lo, hi].
TEST(DistributionFunctions, UniformStaysWithinInterval) {
  SimFixture f;
  MakeVar(f, "seed", 32, 3u);
  auto* call = MkSysCall(
      f.arena, "$dist_uniform",
      {MkId(f.arena, "seed"), MkInt(f.arena, 10u), MkInt(f.arena, 20u)});
  for (int i = 0; i < 100; ++i) {
    int32_t v = static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64());
    EXPECT_GE(v, 10);
    EXPECT_LE(v, 20);
  }
}

// §20.14.2 (shall): a distribution function shall always return the same value
// given the same seed. With a literal seed each call reseeds identically, so
// the result repeats.
TEST(DistributionFunctions, SameSeedReturnsSameValue) {
  SimFixture f;
  auto make = [&]() {
    return MkSysCall(
        f.arena, "$dist_uniform",
        {MkInt(f.arena, 7u), MkInt(f.arena, 0u), MkInt(f.arena, 1000000u)});
  };
  auto first = EvalExpr(make(), f.ctx, f.arena).ToUint64();
  auto second = EvalExpr(make(), f.ctx, f.arena).ToUint64();
  EXPECT_EQ(first, second);
}

// §20.14.2: the seed controls the returned numbers, so different seeds select
// different streams.
TEST(DistributionFunctions, DifferentSeedsDiffer) {
  SimFixture f;
  auto stream_for = [&](uint64_t seed) {
    f.ctx.SeedUrandom(0);  // start each run from a clean generator state
    auto* var = f.ctx.FindVariable("seed");
    if (var == nullptr) var = MakeVar(f, "seed", 32, seed);
    var->value = MakeLogic4VecVal(f.arena, 32, seed);
    auto* call = MkSysCall(
        f.arena, "$dist_uniform",
        {MkId(f.arena, "seed"), MkInt(f.arena, 0u), MkInt(f.arena, 1000000u)});
    return DistStream(f, call, 6);
  };
  EXPECT_NE(stream_for(1u), stream_for(2u));
}

// §20.14.2: the seed is an inout argument — a value is passed in and a
// different value is returned. A seed that names a variable is advanced by the
// call, so the variable changes and successive draws are not pinned to one
// value.
TEST(DistributionFunctions, SeedIsInoutAndAdvances) {
  SimFixture f;
  MakeVar(f, "seed", 32, 1u);
  auto* call = MkSysCall(
      f.arena, "$dist_uniform",
      {MkId(f.arena, "seed"), MkInt(f.arena, 0u), MkInt(f.arena, 1000000u)});

  uint64_t before = f.ctx.FindVariable("seed")->value.ToUint64();
  auto stream = DistStream(f, call, 8);
  uint64_t after = f.ctx.FindVariable("seed")->value.ToUint64();

  EXPECT_NE(before, after);
  std::set<int32_t> distinct(stream.begin(), stream.end());
  EXPECT_GT(distinct.size(), 1u);
}

// §20.14.2: because the operation is repeatable, re-initializing the inout seed
// variable to its original value replays the identical stream.
TEST(DistributionFunctions, ReinitializedSeedReplaysStream) {
  SimFixture f;
  auto* call = MkSysCall(
      f.arena, "$dist_uniform",
      {MkId(f.arena, "seed"), MkInt(f.arena, 0u), MkInt(f.arena, 1000000u)});

  MakeVar(f, "seed", 32, 24680u);
  auto first = DistStream(f, call, 6);
  f.ctx.FindVariable("seed")->value = MakeLogic4VecVal(f.arena, 32, 24680u);
  auto second = DistStream(f, call, 6);

  EXPECT_EQ(first, second);
}

// §20.14.2 (shall): the mean argument shall be greater than 0 for the
// distributions that use it; a non-positive mean is reported.
TEST(DistributionFunctions, NonPositiveMeanIsReported) {
  SimFixture f;
  auto* call = MkSysCall(f.arena, "$dist_exponential",
                         {MkInt(f.arena, 1u), MkInt(f.arena, 0u)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// §20.14.2: a positive mean satisfies the requirement and draws silently.
TEST(DistributionFunctions, PositiveMeanIsAccepted) {
  SimFixture f;
  auto* call = MkSysCall(f.arena, "$dist_exponential",
                         {MkInt(f.arena, 1u), MkInt(f.arena, 5u)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// §20.14.2: the positivity requirement names exponential, poisson, chi-square,
// t, and erlang — not $dist_normal, whose mean may be zero or negative, so it
// draws without complaint.
TEST(DistributionFunctions, NormalAllowsNonPositiveMean) {
  SimFixture f;
  auto* call =
      MkSysCall(f.arena, "$dist_normal",
                {MkInt(f.arena, 1u), MkInt(f.arena, 0u), MkInt(f.arena, 4u)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// §20.14.2 (shall): $dist_poisson also takes a mean, so a non-positive mean is
// reported for it too.
TEST(DistributionFunctions, PoissonNonPositiveMeanIsReported) {
  SimFixture f;
  auto* call = MkSysCall(f.arena, "$dist_poisson",
                         {MkInt(f.arena, 1u), MkInt(f.arena, 0u)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// §20.14.2 (shall): the degree_of_freedom argument of $dist_chi_square shall be
// greater than 0; a non-positive value is reported.
TEST(DistributionFunctions, ChiSquareNonPositiveDofIsReported) {
  SimFixture f;
  auto* call = MkSysCall(f.arena, "$dist_chi_square",
                         {MkInt(f.arena, 1u), MkInt(f.arena, 0u)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// §20.14.2 (shall): the same degree_of_freedom requirement applies to $dist_t.
TEST(DistributionFunctions, TNonPositiveDofIsReported) {
  SimFixture f;
  auto* call =
      MkSysCall(f.arena, "$dist_t", {MkInt(f.arena, 1u), MkInt(f.arena, 0u)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// §20.14.2 (shall): for $dist_erlang both k_stage and mean shall be greater
// than 0, so a non-positive k_stage is reported.
TEST(DistributionFunctions, ErlangNonPositiveKStageIsReported) {
  SimFixture f;
  auto* call =
      MkSysCall(f.arena, "$dist_erlang",
                {MkInt(f.arena, 1u), MkInt(f.arena, 0u), MkInt(f.arena, 7u)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// §20.14.2 (shall): erlang's mean is the second of its two positive arguments;
// with a valid k_stage a non-positive mean is the value that is reported.
TEST(DistributionFunctions, ErlangNonPositiveMeanIsReported) {
  SimFixture f;
  auto* call =
      MkSysCall(f.arena, "$dist_erlang",
                {MkInt(f.arena, 1u), MkInt(f.arena, 2u), MkInt(f.arena, 0u)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// §20.14.2 (shall, edge): the positivity check treats the argument as a signed
// integer, so a negative mean — not only zero — is reported.
TEST(DistributionFunctions, NegativeMeanIsReported) {
  SimFixture f;
  MakeVar(f, "neg", 32, 0xFFFFFFFFu);  // -1 as a signed 32-bit value
  auto* call = MkSysCall(f.arena, "$dist_exponential",
                         {MkInt(f.arena, 1u), MkId(f.arena, "neg")});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// §20.14.2 (edge): when $dist_uniform's start equals its end the bounding
// interval is a single point, so every draw returns that value.
TEST(DistributionFunctions, UniformDegenerateInterval) {
  SimFixture f;
  MakeVar(f, "seed", 32, 5u);
  auto* call = MkSysCall(
      f.arena, "$dist_uniform",
      {MkId(f.arena, "seed"), MkInt(f.arena, 42u), MkInt(f.arena, 42u)});
  for (int i = 0; i < 16; ++i) {
    int32_t v = static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64());
    EXPECT_EQ(v, 42);
  }
}

// §20.14.2: the distribution functions return integer values, so the result is
// not flagged as a real number.
TEST(DistributionFunctions, ResultIsIntegerNotReal) {
  SimFixture f;
  auto* call =
      MkSysCall(f.arena, "$dist_uniform",
                {MkInt(f.arena, 1u), MkInt(f.arena, 0u), MkInt(f.arena, 100u)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_FALSE(result.is_real);
}

}  // namespace
