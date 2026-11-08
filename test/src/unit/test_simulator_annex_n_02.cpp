#include <gtest/gtest.h>

#include <cmath>
#include <cstdint>
#include <cstring>
#include <utility>
#include <vector>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/probabilistic_distribution.h"

using namespace delta;

namespace {

double RefUniform(int32_t* seed, int32_t start, int32_t end) {
  const double kD = 0.00000011920928955078125;
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

int32_t DistTruncate(double r) {
  return r >= 0 ? static_cast<int32_t>(r) : static_cast<int32_t>(r - 1);
}

int32_t GoldenRtlDistUniformIncEnd(int32_t* seed, int32_t start, int32_t end) {
  end++;
  int32_t i = DistTruncate(RefUniform(seed, start, end));
  if (i < start) i = start;
  if (i >= end) i = end - 1;
  return i;
}

int32_t GoldenRtlDistUniformDecStart(int32_t* seed, int32_t start,
                                     int32_t end) {
  start--;
  int32_t i = DistTruncate(RefUniform(seed, start, end) + 1.0);
  if (i <= start) i = start + 1;
  if (i > end) i = end;
  return i;
}

int32_t GoldenRtlDistUniformFullRange(int32_t* seed, int32_t start,
                                      int32_t end) {
  double r = (RefUniform(seed, start, end) + 2147483648.0) / 4294967295.0;
  r = r * 4294967296.0 - 2147483648.0;
  return DistTruncate(r);
}

int32_t GoldenRtlDistUniform(int32_t* seed, int32_t start, int32_t end) {
  if (start >= end) return start;
  if (end != INT32_MAX) return GoldenRtlDistUniformIncEnd(seed, start, end);
  if (start != INT32_MIN) return GoldenRtlDistUniformDecStart(seed, start, end);
  return GoldenRtlDistUniformFullRange(seed, start, end);
}

int32_t GoldenRtlDistNormal(int32_t* seed, int32_t mean, int32_t sd) {
  return RoundDistResult(RefNormal(seed, mean, sd));
}
int32_t GoldenRtlDistExponential(int32_t* seed, int32_t mean) {
  if (mean <= 0) return 0;
  return RoundDistResult(RefExponential(seed, mean));
}
int32_t GoldenRtlDistPoisson(int32_t* seed, int32_t mean) {
  if (mean <= 0) return 0;
  return RefPoisson(seed, mean);
}
int32_t GoldenRtlDistChiSquare(int32_t* seed, int32_t df) {
  if (df <= 0) return 0;
  return RoundDistResult(RefChiSquare(seed, df));
}
int32_t GoldenRtlDistT(int32_t* seed, int32_t df) {
  if (df <= 0) return 0;
  return RoundDistResult(RefT(seed, df));
}
int32_t GoldenRtlDistErlang(int32_t* seed, int32_t k, int32_t mean) {
  if (k <= 0) return 0;
  return RoundDistResult(RefErlangian(seed, k, mean));
}

int32_t EvalDist(SimFixture& f, const char* name, std::vector<Expr*> args) {
  auto* call = MkSysCall(f.arena, name, std::move(args));
  return static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64());
}

const int32_t kSeeds[] = {1, 7, 42, 12345, 65535, 99999, 259341593, 0};

TEST(ProbabilisticDistributionAlgorithm, UniformMatchesReference) {
  for (int32_t s : kSeeds) {
    int32_t rseed = s;
    int32_t expected = GoldenRtlDistUniform(&rseed, 0, 1000);
    SimFixture f;
    int32_t got = EvalDist(f, "$dist_uniform",
                           {MkInt(f.arena, static_cast<uint32_t>(s)),
                            MkInt(f.arena, 0u), MkInt(f.arena, 1000u)});
    EXPECT_EQ(got, expected) << "seed=" << s;
  }
}

TEST(ProbabilisticDistributionAlgorithm, UniformEndAtMaxMatchesReference) {
  for (int32_t s : kSeeds) {
    int32_t rseed = s;
    int32_t expected = GoldenRtlDistUniform(&rseed, 100, INT32_MAX);
    SimFixture f;
    int32_t got = EvalDist(
        f, "$dist_uniform",
        {MkInt(f.arena, static_cast<uint32_t>(s)), MkInt(f.arena, 100u),
         MkInt(f.arena, static_cast<uint32_t>(INT32_MAX))});
    EXPECT_EQ(got, expected) << "seed=" << s;
  }
}

TEST(ProbabilisticDistributionAlgorithm, UniformFullRangeMatchesReference) {
  for (int32_t s : kSeeds) {
    int32_t rseed = s;
    int32_t expected = GoldenRtlDistUniform(&rseed, INT32_MIN, INT32_MAX);
    SimFixture f;
    int32_t got = EvalDist(f, "$dist_uniform",
                           {MkInt(f.arena, static_cast<uint32_t>(s)),
                            MkInt(f.arena, static_cast<uint32_t>(INT32_MIN)),
                            MkInt(f.arena, static_cast<uint32_t>(INT32_MAX))});
    EXPECT_EQ(got, expected) << "seed=" << s;
  }
}

TEST(ProbabilisticDistributionAlgorithm, NormalMatchesReference) {
  for (int32_t s : kSeeds) {
    int32_t rseed = s;
    int32_t expected = GoldenRtlDistNormal(&rseed, 100, 10);
    SimFixture f;
    int32_t got = EvalDist(f, "$dist_normal",
                           {MkInt(f.arena, static_cast<uint32_t>(s)),
                            MkInt(f.arena, 100u), MkInt(f.arena, 10u)});
    EXPECT_EQ(got, expected) << "seed=" << s;
  }
}

TEST(ProbabilisticDistributionAlgorithm, NormalSignedRoundingMatchesReference) {
  for (int32_t s : kSeeds) {
    int32_t rseed = s;
    int32_t expected = GoldenRtlDistNormal(&rseed, 0, 50);
    SimFixture f;
    int32_t got = EvalDist(f, "$dist_normal",
                           {MkInt(f.arena, static_cast<uint32_t>(s)),
                            MkInt(f.arena, 0u), MkInt(f.arena, 50u)});
    EXPECT_EQ(got, expected) << "seed=" << s;
  }
}

TEST(ProbabilisticDistributionAlgorithm, ExponentialMatchesReference) {
  for (int32_t s : kSeeds) {
    int32_t rseed = s;
    int32_t expected = GoldenRtlDistExponential(&rseed, 25);
    SimFixture f;
    int32_t got = EvalDist(
        f, "$dist_exponential",
        {MkInt(f.arena, static_cast<uint32_t>(s)), MkInt(f.arena, 25u)});
    EXPECT_EQ(got, expected) << "seed=" << s;
  }
}

TEST(ProbabilisticDistributionAlgorithm, PoissonMatchesReference) {
  for (int32_t s : kSeeds) {
    int32_t rseed = s;
    int32_t expected = GoldenRtlDistPoisson(&rseed, 5);
    SimFixture f;
    int32_t got = EvalDist(
        f, "$dist_poisson",
        {MkInt(f.arena, static_cast<uint32_t>(s)), MkInt(f.arena, 5u)});
    EXPECT_EQ(got, expected) << "seed=" << s;
  }
}

TEST(ProbabilisticDistributionAlgorithm, ChiSquareMatchesReference) {
  for (int32_t s : kSeeds) {
    int32_t rseed = s;
    int32_t expected = GoldenRtlDistChiSquare(&rseed, 5);
    SimFixture f;
    int32_t got = EvalDist(
        f, "$dist_chi_square",
        {MkInt(f.arena, static_cast<uint32_t>(s)), MkInt(f.arena, 5u)});
    EXPECT_EQ(got, expected) << "seed=" << s;
  }
}

TEST(ProbabilisticDistributionAlgorithm, TMatchesReference) {
  for (int32_t s : kSeeds) {
    int32_t rseed = s;
    int32_t expected = GoldenRtlDistT(&rseed, 5);
    SimFixture f;
    int32_t got = EvalDist(
        f, "$dist_t",
        {MkInt(f.arena, static_cast<uint32_t>(s)), MkInt(f.arena, 5u)});
    EXPECT_EQ(got, expected) << "seed=" << s;
  }
}

TEST(ProbabilisticDistributionAlgorithm, ErlangMatchesReference) {
  for (int32_t s : kSeeds) {
    int32_t rseed = s;
    int32_t expected = GoldenRtlDistErlang(&rseed, 3, 7);
    SimFixture f;
    int32_t got = EvalDist(f, "$dist_erlang",
                           {MkInt(f.arena, static_cast<uint32_t>(s)),
                            MkInt(f.arena, 3u), MkInt(f.arena, 7u)});
    EXPECT_EQ(got, expected) << "seed=" << s;
  }
}

TEST(ProbabilisticDistributionAlgorithm, SeedAdvancesByReferenceLcg) {
  SimFixture f;
  MakeVar(f, "seed", 32, 1u);
  auto* call = MkSysCall(
      f.arena, "$dist_uniform",
      {MkId(f.arena, "seed"), MkInt(f.arena, 0u), MkInt(f.arena, 1000u)});
  EvalExpr(call, f.ctx, f.arena);

  int32_t rseed = 1;
  GoldenRtlDistUniform(&rseed, 0, 1000);
  auto after =
      static_cast<uint32_t>(f.ctx.FindVariable("seed")->value.ToUint64());
  EXPECT_EQ(after, static_cast<uint32_t>(rseed));
}

TEST(ProbabilisticDistributionAlgorithm, UniformDegenerateReturnsStart) {
  SimFixture f;
  for (int i = 0; i < 8; ++i) {
    int32_t got = EvalDist(
        f, "$dist_uniform",
        {MkInt(f.arena, 13u), MkInt(f.arena, 55u), MkInt(f.arena, 55u)});
    EXPECT_EQ(got, 55);
  }
}

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

TEST(ProbabilisticDistributionAlgorithm, RoundingIsTheAnnexsIdiom) {
  const double kJustBelowHalf = 0.49999999999999994;
  EXPECT_EQ(delta::RtlDistRound(kJustBelowHalf), 1);
  EXPECT_EQ(delta::RtlDistRound(-kJustBelowHalf), -1);
  EXPECT_EQ(std::lround(kJustBelowHalf), 0);
  EXPECT_EQ(delta::RtlDistRound(2.5), 3);
  EXPECT_EQ(delta::RtlDistRound(-2.5), -3);
  EXPECT_EQ(delta::RtlDistRound(0.4), 0);
  EXPECT_EQ(delta::RtlDistRound(-0.4), 0);
  EXPECT_EQ(delta::RtlDistRound(0.0), 0);
}

TEST(ProbabilisticDistributionAlgorithm, TheSevenCFunctionsMatchTheReference) {
  for (int32_t s : kSeeds) {
    int32_t g = s;
    int32_t p = s;
    EXPECT_EQ(delta::RtlDistUniform(&p, -5, 5),
              GoldenRtlDistUniform(&g, -5, 5));
    EXPECT_EQ(delta::RtlDistNormal(&p, 10, 3), GoldenRtlDistNormal(&g, 10, 3));
    EXPECT_EQ(delta::RtlDistExponential(&p, 4),
              GoldenRtlDistExponential(&g, 4));
    EXPECT_EQ(delta::RtlDistPoisson(&p, 6), GoldenRtlDistPoisson(&g, 6));
    EXPECT_EQ(delta::RtlDistChiSquare(&p, 5), GoldenRtlDistChiSquare(&g, 5));
    EXPECT_EQ(delta::RtlDistT(&p, 4), GoldenRtlDistT(&g, 4));
    EXPECT_EQ(delta::RtlDistErlang(&p, 3, 7), GoldenRtlDistErlang(&g, 3, 7));
    EXPECT_EQ(p, g) << "seed=" << s;
  }
}

}  // namespace
