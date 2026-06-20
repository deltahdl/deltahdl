#include <gtest/gtest.h>

#include <cmath>
#include <cstdint>
#include <cstring>
#include <utility>
#include <vector>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

// Annex N.2 gives the reference C source that defines the exact numeric
// behavior of the probabilistic distribution system functions ($dist_uniform,
// $dist_normal, $dist_exponential, $dist_poisson, $dist_chi_square, $dist_t,
// $dist_erlang). The block below is an INDEPENDENT transcription of that
// source, used as a golden model: the simulator's evaluator
// (src/simulator/eval_math.cpp) must reproduce these values exactly for the
// same seed and arguments. Because the algorithm is fully deterministic in the
// seed, an exact match is the strongest possible evidence that production
// applies the §N.2 algorithm.

namespace {

double RefUniform(int32_t* seed, int32_t start, int32_t end) {
  const double kD = 0.00000011920928955078125;  // 2^-23
  double a = 0.0;
  double b = 0.0;
  if (*seed == 0) *seed = 259341593;
  if (start >= end) {
    a = 0.0;
    b = 2147483647.0;
  } else {
    a = static_cast<double>(start);
    b = static_cast<double>(end);
  }
  *seed = static_cast<int32_t>(69069u * static_cast<uint32_t>(*seed) + 1u);
  uint32_t bits = (static_cast<uint32_t>(*seed) >> 9) | 0x3f800000u;
  float fs = 0.0F;
  std::memcpy(&fs, &bits, sizeof(fs));
  auto c = static_cast<double>(fs);
  c = c + (c * kD);
  c = ((b - a) * (c - 1.0)) + a;
  return c;
}

double RefNormal(int32_t* seed, int32_t mean, int32_t deviation) {
  double v1 = 0.0, v2 = 0.0, s = 1.0;
  while (s >= 1.0 || s == 0.0) {
    v1 = RefUniform(seed, -1, 1);
    v2 = RefUniform(seed, -1, 1);
    s = v1 * v1 + v2 * v2;
  }
  s = v1 * std::sqrt(-2.0 * std::log(s) / s);
  return s * static_cast<double>(deviation) + static_cast<double>(mean);
}

double RefExponential(int32_t* seed, int32_t mean) {
  double n = RefUniform(seed, 0, 1);
  if (n != 0) n = -std::log(n) * mean;
  return n;
}

int32_t RefPoisson(int32_t* seed, int32_t mean) {
  int32_t n = 0;
  double q = -static_cast<double>(mean);
  double p = std::exp(q);
  q = RefUniform(seed, 0, 1);
  while (p < q) {
    n++;
    q = RefUniform(seed, 0, 1) * q;
  }
  return n;
}

double RefChiSquare(int32_t* seed, int32_t deg_of_free) {
  double x = 0.0;
  if (deg_of_free % 2) {
    x = RefNormal(seed, 0, 1);
    x = x * x;
  } else {
    x = 0.0;
  }
  for (int32_t k = 2; k <= deg_of_free; k += 2) {
    x = x + 2 * RefExponential(seed, 1);
  }
  return x;
}

double RefT(int32_t* seed, int32_t deg_of_free) {
  double chi2 = RefChiSquare(seed, deg_of_free);
  double div = chi2 / static_cast<double>(deg_of_free);
  double root = std::sqrt(div);
  return RefNormal(seed, 0, 1) / root;
}

double RefErlangian(int32_t* seed, int32_t k, int32_t mean) {
  double x = 1.0;
  for (int32_t i = 1; i <= k; i++) x = x * RefUniform(seed, 0, 1);
  auto a = static_cast<double>(mean);
  auto b = static_cast<double>(k);
  return -a * std::log(x) / b;
}

int32_t RoundDistResult(double r) {
  if (r >= 0) return static_cast<int32_t>(r + 0.5);
  r = -r;
  return -static_cast<int32_t>(r + 0.5);
}

int32_t RtlDistUniform(int32_t* seed, int32_t start, int32_t end) {
  if (start >= end) return start;
  int32_t i = 0;
  if (end != INT32_MAX) {
    end++;
    double r = RefUniform(seed, start, end);
    i = r >= 0 ? static_cast<int32_t>(r) : static_cast<int32_t>(r - 1);
    if (i < start) i = start;
    if (i >= end) i = end - 1;
  } else if (start != INT32_MIN) {
    start--;
    double r = RefUniform(seed, start, end) + 1.0;
    i = r >= 0 ? static_cast<int32_t>(r) : static_cast<int32_t>(r - 1);
    if (i <= start) i = start + 1;
    if (i > end) i = end;
  } else {
    double r = (RefUniform(seed, start, end) + 2147483648.0) / 4294967295.0;
    r = r * 4294967296.0 - 2147483648.0;
    i = r >= 0 ? static_cast<int32_t>(r) : static_cast<int32_t>(r - 1);
  }
  return i;
}

int32_t RtlDistNormal(int32_t* seed, int32_t mean, int32_t sd) {
  return RoundDistResult(RefNormal(seed, mean, sd));
}
int32_t RtlDistExponential(int32_t* seed, int32_t mean) {
  if (mean <= 0) return 0;
  return RoundDistResult(RefExponential(seed, mean));
}
int32_t RtlDistPoisson(int32_t* seed, int32_t mean) {
  if (mean <= 0) return 0;
  return RefPoisson(seed, mean);
}
int32_t RtlDistChiSquare(int32_t* seed, int32_t df) {
  if (df <= 0) return 0;
  return RoundDistResult(RefChiSquare(seed, df));
}
int32_t RtlDistT(int32_t* seed, int32_t df) {
  if (df <= 0) return 0;
  return RoundDistResult(RefT(seed, df));
}
int32_t RtlDistErlang(int32_t* seed, int32_t k, int32_t mean) {
  if (k <= 0) return 0;
  return RoundDistResult(RefErlangian(seed, k, mean));
}

// Evaluate a $dist_* system call with a literal seed and return its 32-bit
// result through the production evaluator.
int32_t EvalDist(SimFixture& f, const char* name, std::vector<Expr*> args) {
  auto* call = MkSysCall(f.arena, name, std::move(args));
  return static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64());
}

const int32_t kSeeds[] = {1, 7, 42, 12345, 65535, 99999, 259341593, 0};

// §N.2 rtl_dist_uniform: production reproduces the reference value exactly,
// including the seed advance, the rounding, and the [start, end] clamping.
TEST(ProbabilisticDistributionAlgorithm, UniformMatchesReference) {
  for (int32_t s : kSeeds) {
    int32_t rseed = s;
    int32_t expected = RtlDistUniform(&rseed, 0, 1000);
    SimFixture f;
    int32_t got = EvalDist(f, "$dist_uniform",
                           {MkInt(f.arena, static_cast<uint32_t>(s)),
                            MkInt(f.arena, 0u), MkInt(f.arena, 1000u)});
    EXPECT_EQ(got, expected) << "seed=" << s;
  }
}

// §N.2 rtl_dist_uniform: when end is the maximum representable value the
// reference takes a distinct branch (it decrements start instead of
// incrementing end). The production evaluator must match it exactly.
TEST(ProbabilisticDistributionAlgorithm, UniformEndAtMaxMatchesReference) {
  for (int32_t s : kSeeds) {
    int32_t rseed = s;
    int32_t expected = RtlDistUniform(&rseed, 100, INT32_MAX);
    SimFixture f;
    int32_t got = EvalDist(
        f, "$dist_uniform",
        {MkInt(f.arena, static_cast<uint32_t>(s)), MkInt(f.arena, 100u),
         MkInt(f.arena, static_cast<uint32_t>(INT32_MAX))});
    EXPECT_EQ(got, expected) << "seed=" << s;
  }
}

// §N.2 rtl_dist_uniform: spanning the whole signed range (start at the minimum,
// end at the maximum) drives the reference's third branch, which rescales the
// draw across the full 32-bit range. Production must reproduce it exactly.
TEST(ProbabilisticDistributionAlgorithm, UniformFullRangeMatchesReference) {
  for (int32_t s : kSeeds) {
    int32_t rseed = s;
    int32_t expected = RtlDistUniform(&rseed, INT32_MIN, INT32_MAX);
    SimFixture f;
    int32_t got = EvalDist(f, "$dist_uniform",
                           {MkInt(f.arena, static_cast<uint32_t>(s)),
                            MkInt(f.arena, static_cast<uint32_t>(INT32_MIN)),
                            MkInt(f.arena, static_cast<uint32_t>(INT32_MAX))});
    EXPECT_EQ(got, expected) << "seed=" << s;
  }
}

// §N.2 rtl_dist_normal: the Marsaglia polar method is reproduced exactly.
TEST(ProbabilisticDistributionAlgorithm, NormalMatchesReference) {
  for (int32_t s : kSeeds) {
    int32_t rseed = s;
    int32_t expected = RtlDistNormal(&rseed, 100, 10);
    SimFixture f;
    int32_t got = EvalDist(f, "$dist_normal",
                           {MkInt(f.arena, static_cast<uint32_t>(s)),
                            MkInt(f.arena, 100u), MkInt(f.arena, 10u)});
    EXPECT_EQ(got, expected) << "seed=" << s;
  }
}

// §N.2 rtl_dist_normal: with a zero mean and a wide deviation the draw
// straddles zero, so production must also reproduce the reference's
// sign-preserving rounding for negative results, not only positive ones.
TEST(ProbabilisticDistributionAlgorithm, NormalSignedRoundingMatchesReference) {
  for (int32_t s : kSeeds) {
    int32_t rseed = s;
    int32_t expected = RtlDistNormal(&rseed, 0, 50);
    SimFixture f;
    int32_t got = EvalDist(f, "$dist_normal",
                           {MkInt(f.arena, static_cast<uint32_t>(s)),
                            MkInt(f.arena, 0u), MkInt(f.arena, 50u)});
    EXPECT_EQ(got, expected) << "seed=" << s;
  }
}

// §N.2 rtl_dist_exponential: the inverse-transform draw is reproduced exactly.
TEST(ProbabilisticDistributionAlgorithm, ExponentialMatchesReference) {
  for (int32_t s : kSeeds) {
    int32_t rseed = s;
    int32_t expected = RtlDistExponential(&rseed, 25);
    SimFixture f;
    int32_t got = EvalDist(
        f, "$dist_exponential",
        {MkInt(f.arena, static_cast<uint32_t>(s)), MkInt(f.arena, 25u)});
    EXPECT_EQ(got, expected) << "seed=" << s;
  }
}

// §N.2 rtl_dist_poisson: the product-counting draw is reproduced exactly.
TEST(ProbabilisticDistributionAlgorithm, PoissonMatchesReference) {
  for (int32_t s : kSeeds) {
    int32_t rseed = s;
    int32_t expected = RtlDistPoisson(&rseed, 5);
    SimFixture f;
    int32_t got = EvalDist(
        f, "$dist_poisson",
        {MkInt(f.arena, static_cast<uint32_t>(s)), MkInt(f.arena, 5u)});
    EXPECT_EQ(got, expected) << "seed=" << s;
  }
}

// §N.2 rtl_dist_chi_square: the squared-normal plus exponential-pairs sum is
// reproduced exactly. This is the strongest guard against the prior behavior,
// which returned a raw 32-bit random instead of the §N.2 algorithm.
TEST(ProbabilisticDistributionAlgorithm, ChiSquareMatchesReference) {
  for (int32_t s : kSeeds) {
    int32_t rseed = s;
    int32_t expected = RtlDistChiSquare(&rseed, 5);
    SimFixture f;
    int32_t got = EvalDist(
        f, "$dist_chi_square",
        {MkInt(f.arena, static_cast<uint32_t>(s)), MkInt(f.arena, 5u)});
    EXPECT_EQ(got, expected) << "seed=" << s;
  }
}

// §N.2 rtl_dist_t: a normal over the root of a normalized chi-square is
// reproduced exactly.
TEST(ProbabilisticDistributionAlgorithm, TMatchesReference) {
  for (int32_t s : kSeeds) {
    int32_t rseed = s;
    int32_t expected = RtlDistT(&rseed, 5);
    SimFixture f;
    int32_t got = EvalDist(
        f, "$dist_t",
        {MkInt(f.arena, static_cast<uint32_t>(s)), MkInt(f.arena, 5u)});
    EXPECT_EQ(got, expected) << "seed=" << s;
  }
}

// §N.2 rtl_dist_erlang: the k-fold uniform product is reproduced exactly.
TEST(ProbabilisticDistributionAlgorithm, ErlangMatchesReference) {
  for (int32_t s : kSeeds) {
    int32_t rseed = s;
    int32_t expected = RtlDistErlang(&rseed, 3, 7);
    SimFixture f;
    int32_t got = EvalDist(f, "$dist_erlang",
                           {MkInt(f.arena, static_cast<uint32_t>(s)),
                            MkInt(f.arena, 3u), MkInt(f.arena, 7u)});
    EXPECT_EQ(got, expected) << "seed=" << s;
  }
}

// §N.2 uniform(): the seed is advanced by the 69069 linear-congruential step.
// After a draw the inout seed variable holds exactly the state the reference
// algorithm leaves behind, which observes both the LCG and the write-back.
TEST(ProbabilisticDistributionAlgorithm, SeedAdvancesByReferenceLcg) {
  SimFixture f;
  MakeVar(f, "seed", 32, 1u);
  auto* call = MkSysCall(
      f.arena, "$dist_uniform",
      {MkId(f.arena, "seed"), MkInt(f.arena, 0u), MkInt(f.arena, 1000u)});
  EvalExpr(call, f.ctx, f.arena);

  int32_t rseed = 1;
  RtlDistUniform(&rseed, 0, 1000);  // advance the golden seed identically
  auto after =
      static_cast<uint32_t>(f.ctx.FindVariable("seed")->value.ToUint64());
  EXPECT_EQ(after, static_cast<uint32_t>(rseed));
}

// §N.2 rtl_dist_uniform: when start >= end the bounding interval is a single
// point, so the reference returns start without drawing.
TEST(ProbabilisticDistributionAlgorithm, UniformDegenerateReturnsStart) {
  SimFixture f;
  for (int i = 0; i < 8; ++i) {
    int32_t got = EvalDist(
        f, "$dist_uniform",
        {MkInt(f.arena, 13u), MkInt(f.arena, 55u), MkInt(f.arena, 55u)});
    EXPECT_EQ(got, 55);
  }
}

// §N.2 rtl_dist_uniform: every draw lands within [start, end] thanks to the
// reference's rounding-and-clamp step.
TEST(ProbabilisticDistributionAlgorithm, UniformStaysInRange) {
  SimFixture f;
  MakeVar(f, "seed", 32, 3u);
  auto* call = MkSysCall(
      f.arena, "$dist_uniform",
      {MkId(f.arena, "seed"), MkInt(f.arena, 10u), MkInt(f.arena, 20u)});
  for (int i = 0; i < 200; ++i) {
    int32_t v = static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64());
    EXPECT_GE(v, 10);
    EXPECT_LE(v, 20);
  }
}

// §N.2: the rtl_dist_* wrappers for exponential, poisson, chi-square, t, and
// erlang return 0 when the argument the reference requires to be positive is
// not (the reference's "else i = 0" branch). $dist_normal has no such guard.
TEST(ProbabilisticDistributionAlgorithm, NonPositiveArgumentReturnsZero) {
  SimFixture f;
  EXPECT_EQ(EvalDist(f, "$dist_exponential",
                     {MkInt(f.arena, 1u), MkInt(f.arena, 0u)}),
            0);
  EXPECT_EQ(
      EvalDist(f, "$dist_poisson", {MkInt(f.arena, 1u), MkInt(f.arena, 0u)}),
      0);
  EXPECT_EQ(
      EvalDist(f, "$dist_chi_square", {MkInt(f.arena, 1u), MkInt(f.arena, 0u)}),
      0);
  EXPECT_EQ(EvalDist(f, "$dist_t", {MkInt(f.arena, 1u), MkInt(f.arena, 0u)}),
            0);
  EXPECT_EQ(
      EvalDist(f, "$dist_erlang",
               {MkInt(f.arena, 1u), MkInt(f.arena, 0u), MkInt(f.arena, 7u)}),
      0);
}

// §N.2 uniform(): the algorithm is fully determined by the seed, so evaluating
// any distribution twice with the same literal seed yields the same value. This
// observes the production result directly, without a reference oracle.
TEST(ProbabilisticDistributionAlgorithm, AllDistributionsAreDeterministic) {
  SimFixture f;
  auto twice_equal = [&](const char* name, std::vector<Expr*> a,
                         std::vector<Expr*> b) {
    EXPECT_EQ(EvalDist(f, name, std::move(a)), EvalDist(f, name, std::move(b)))
        << name;
  };
  auto seed = [&]() { return MkInt(f.arena, 7u); };
  twice_equal("$dist_uniform",
              {seed(), MkInt(f.arena, 0u), MkInt(f.arena, 99u)},
              {seed(), MkInt(f.arena, 0u), MkInt(f.arena, 99u)});
  twice_equal("$dist_normal", {seed(), MkInt(f.arena, 4u), MkInt(f.arena, 2u)},
              {seed(), MkInt(f.arena, 4u), MkInt(f.arena, 2u)});
  twice_equal("$dist_exponential", {seed(), MkInt(f.arena, 9u)},
              {seed(), MkInt(f.arena, 9u)});
  twice_equal("$dist_poisson", {seed(), MkInt(f.arena, 4u)},
              {seed(), MkInt(f.arena, 4u)});
  twice_equal("$dist_chi_square", {seed(), MkInt(f.arena, 5u)},
              {seed(), MkInt(f.arena, 5u)});
  twice_equal("$dist_t", {seed(), MkInt(f.arena, 5u)},
              {seed(), MkInt(f.arena, 5u)});
  twice_equal("$dist_erlang", {seed(), MkInt(f.arena, 3u), MkInt(f.arena, 7u)},
              {seed(), MkInt(f.arena, 3u), MkInt(f.arena, 7u)});
}

// §N.2: exponential, poisson, and chi-square are built from non-negative
// quantities (a scaled negative log, a count, and a sum of squares and
// exponentials), so their integer results are never negative. Asserting this on
// the production output observes the algorithm's structure without an oracle.
TEST(ProbabilisticDistributionAlgorithm, DistributionsAreNonNegative) {
  for (int32_t s : kSeeds) {
    SimFixture f;
    EXPECT_GE(EvalDist(f, "$dist_exponential",
                       {MkInt(f.arena, static_cast<uint32_t>(s)),
                        MkInt(f.arena, 25u)}),
              0)
        << "seed=" << s;
    EXPECT_GE(EvalDist(f, "$dist_poisson",
                       {MkInt(f.arena, static_cast<uint32_t>(s)),
                        MkInt(f.arena, 5u)}),
              0)
        << "seed=" << s;
    EXPECT_GE(EvalDist(f, "$dist_chi_square",
                       {MkInt(f.arena, static_cast<uint32_t>(s)),
                        MkInt(f.arena, 5u)}),
              0)
        << "seed=" << s;
  }
}

// §N.2 chi_square(): the result is a small statistic on the order of its
// degrees of freedom, never the full-width 32-bit random the function returned
// before the §N.2 algorithm was implemented. A loose magnitude bound observes
// that the production code now runs the algorithm rather than echoing a raw
// draw.
TEST(ProbabilisticDistributionAlgorithm, ChiSquareIsAlgorithmicNotRawRandom) {
  for (int32_t s : kSeeds) {
    SimFixture f;
    int32_t v = EvalDist(
        f, "$dist_chi_square",
        {MkInt(f.arena, static_cast<uint32_t>(s)), MkInt(f.arena, 5u)});
    EXPECT_GE(v, 0) << "seed=" << s;
    EXPECT_LT(v, 100000) << "seed=" << s;
  }
}

}  // namespace
