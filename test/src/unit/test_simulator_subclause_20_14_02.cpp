#include <gtest/gtest.h>

#include <charconv>
#include <string>
#include <system_error>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"

using namespace delta;

namespace {

std::vector<long long> Values(const std::string& out) {
  std::vector<long long> vals;
  for (const auto& line : Lines(out)) vals.push_back(std::stoll(line));
  return vals;
}

unsigned WarnCount(const std::string& body) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  integer seed;\n"
      "  integer v;\n"
      "  initial begin\n"
      "    seed = 1;\n" +
          body +
          "  end\n"
          "endmodule\n",
      f);
  return f.diag.WarningCount();
}

TEST(DistributionFunctions, EachFormReturnsInteger) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  integer seed;\n"
      "  integer v;\n"
      "  initial begin\n"
      "    seed = 5;\n"
      "    v = $dist_uniform(seed, 5, 7);      $display(\"%0d\", v);\n"
      "    v = $dist_normal(seed, 50, 10);     $display(\"%0d\", v);\n"
      "    v = $dist_exponential(seed, 5);     $display(\"%0d\", v);\n"
      "    v = $dist_poisson(seed, 10);        $display(\"%0d\", v);\n"
      "    v = $dist_chi_square(seed, 3);      $display(\"%0d\", v);\n"
      "    v = $dist_t(seed, 4);               $display(\"%0d\", v);\n"
      "    v = $dist_erlang(seed, 2, 7);       $display(\"%0d\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  auto lines = Lines(out);
  ASSERT_EQ(lines.size(), 7u);
  for (const auto& line : lines) {
    long long value = 0;
    auto [end, ec] =
        std::from_chars(line.data(), line.data() + line.size(), value);
    EXPECT_EQ(ec, std::errc()) << line;
    EXPECT_EQ(end, line.data() + line.size()) << line;
  }
}

TEST(DistributionFunctions, UniformStaysWithinInterval) {
  std::string src =
      "module t;\n"
      "  integer seed;\n"
      "  integer v;\n"
      "  initial begin\n"
      "    seed = 3;\n";
  for (int i = 0; i < 60; ++i) {
    src += "    v = $dist_uniform(seed, 10, 20); $display(\"%0d\", v);\n";
  }
  src +=
      "  end\n"
      "endmodule\n";
  SimFixture f;
  auto vals = Values(RunCapture(src, f));
  ASSERT_EQ(vals.size(), 60u);
  for (long long v : vals) {
    EXPECT_GE(v, 10);
    EXPECT_LE(v, 20);
  }
}

TEST(DistributionFunctions, UniformBoundsFromVariables) {
  std::string src =
      "module t;\n"
      "  integer seed;\n"
      "  integer lo, hi;\n"
      "  integer v;\n"
      "  initial begin\n"
      "    seed = 3;\n"
      "    lo = 10;\n"
      "    hi = 20;\n";
  for (int i = 0; i < 40; ++i) {
    src += "    v = $dist_uniform(seed, lo, hi); $display(\"%0d\", v);\n";
  }
  src +=
      "  end\n"
      "endmodule\n";
  SimFixture f;
  auto vals = Values(RunCapture(src, f));
  ASSERT_EQ(vals.size(), 40u);
  for (long long v : vals) {
    EXPECT_GE(v, 10);
    EXPECT_LE(v, 20);
  }
}

TEST(DistributionFunctions, DistCallAsDisplayArgument) {
  std::string src =
      "module t;\n"
      "  integer seed;\n"
      "  initial begin\n"
      "    seed = 8;\n";
  for (int i = 0; i < 32; ++i) {
    src += "    $display(\"%0d\", $dist_uniform(seed, 5, 7));\n";
  }
  src +=
      "  end\n"
      "endmodule\n";
  SimFixture f;
  auto vals = Values(RunCapture(src, f));
  ASSERT_EQ(vals.size(), 32u);
  for (long long v : vals) {
    EXPECT_GE(v, 5);
    EXPECT_LE(v, 7);
  }
}

TEST(DistributionFunctions, SameSeedReplaysStream) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  integer seed;\n"
      "  integer a1, a2, b1, b2;\n"
      "  initial begin\n"
      "    seed = 777;\n"
      "    a1 = $dist_uniform(seed, 0, 1000000);\n"
      "    a2 = $dist_uniform(seed, 0, 1000000);\n"
      "    seed = 777;\n"
      "    b1 = $dist_uniform(seed, 0, 1000000);\n"
      "    b2 = $dist_uniform(seed, 0, 1000000);\n"
      "    $display(\"%0d\", a1);\n"
      "    $display(\"%0d\", a2);\n"
      "    $display(\"%0d\", b1);\n"
      "    $display(\"%0d\", b2);\n"
      "  end\n"
      "endmodule\n",
      f);
  auto lines = Lines(out);
  ASSERT_EQ(lines.size(), 4u);
  EXPECT_EQ(lines[0], lines[2]);
  EXPECT_EQ(lines[1], lines[3]);
}

TEST(DistributionFunctions, SeedIsInoutAndAdvances) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  integer seed;\n"
      "  integer v;\n"
      "  initial begin\n"
      "    seed = 12345;\n"
      "    $display(\"%0d\", seed);\n"
      "    v = $dist_uniform(seed, 0, 1000000);\n"
      "    $display(\"%0d\", seed);\n"
      "  end\n"
      "endmodule\n",
      f);
  auto lines = Lines(out);
  ASSERT_EQ(lines.size(), 2u);
  EXPECT_NE(lines[0], lines[1]);
}

TEST(DistributionFunctions, DifferentSeedsGiveDifferentStreams) {
  auto run_with_seed = [](const std::string& seed_value) {
    SimFixture f;
    std::string src =
        "module t;\n"
        "  integer seed;\n"
        "  integer v;\n"
        "  initial begin\n"
        "    seed = " +
        seed_value +
        ";\n"
        "    v = $dist_uniform(seed, 0, 1000000); $display(\"%0d\", v);\n"
        "    v = $dist_uniform(seed, 0, 1000000); $display(\"%0d\", v);\n"
        "    v = $dist_uniform(seed, 0, 1000000); $display(\"%0d\", v);\n"
        "  end\n"
        "endmodule\n";
    return RunCapture(src, f);
  };
  EXPECT_NE(run_with_seed("1"), run_with_seed("2"));
}

TEST(DistributionFunctions, UniformDegenerateInterval) {
  std::string src =
      "module t;\n"
      "  integer seed;\n"
      "  integer v;\n"
      "  initial begin\n"
      "    seed = 5;\n";
  for (int i = 0; i < 16; ++i) {
    src += "    v = $dist_uniform(seed, 42, 42); $display(\"%0d\", v);\n";
  }
  src +=
      "  end\n"
      "endmodule\n";
  SimFixture f;
  auto vals = Values(RunCapture(src, f));
  ASSERT_EQ(vals.size(), 16u);
  for (long long v : vals) EXPECT_EQ(v, 42);
}

TEST(DistributionFunctions, ExponentialMeanPositivity) {
  EXPECT_GE(WarnCount("    v = $dist_exponential(seed, 0);\n"), 1u);
  EXPECT_EQ(WarnCount("    v = $dist_exponential(seed, 5);\n"), 0u);
}

TEST(DistributionFunctions, PoissonMeanPositivity) {
  EXPECT_GE(WarnCount("    v = $dist_poisson(seed, 0);\n"), 1u);
  EXPECT_EQ(WarnCount("    v = $dist_poisson(seed, 10);\n"), 0u);
}

TEST(DistributionFunctions, NormalAllowsNonPositiveMean) {
  EXPECT_EQ(WarnCount("    v = $dist_normal(seed, 0, 4);\n"), 0u);
}

TEST(DistributionFunctions, DegreeOfFreedomPositivity) {
  EXPECT_GE(WarnCount("    v = $dist_chi_square(seed, 0);\n"), 1u);
  EXPECT_EQ(WarnCount("    v = $dist_chi_square(seed, 3);\n"), 0u);
  EXPECT_GE(WarnCount("    v = $dist_t(seed, 0);\n"), 1u);
  EXPECT_EQ(WarnCount("    v = $dist_t(seed, 4);\n"), 0u);
}

TEST(DistributionFunctions, ErlangKStageAndMeanPositivity) {
  EXPECT_GE(WarnCount("    v = $dist_erlang(seed, 0, 7);\n"), 1u);
  EXPECT_GE(WarnCount("    v = $dist_erlang(seed, 2, 0);\n"), 1u);
  EXPECT_EQ(WarnCount("    v = $dist_erlang(seed, 2, 7);\n"), 0u);
}

TEST(DistributionFunctions, NegativeMeanIsReported) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  integer seed;\n"
      "  integer m;\n"
      "  integer v;\n"
      "  initial begin\n"
      "    seed = 1;\n"
      "    m = -1;\n"
      "    v = $dist_exponential(seed, m);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(DistributionFunctions, NonPositiveArgumentWarningNames20_14_2) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  integer seed;\n"
      "  integer v;\n"
      "  initial begin\n"
      "    seed = 1;\n"
      "    v = $dist_poisson(seed, 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(),
      "argument of a distribution function shall be greater", 6, "20.14.2"));
}

TEST(DistributionFunctions, ADrawIsASignedInteger) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  int seed = 5;\n"
                 "  initial $display(\"%0d\", $dist_uniform(seed, -3, -1) < "
                 "0);\n"
                 "endmodule\n",
                 f),
      "1\n");
}

}  // namespace
