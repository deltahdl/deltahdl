// §20.14.2 Distribution functions — the probabilistic RNGs $dist_uniform,
// $dist_normal, $dist_exponential, $dist_poisson, $dist_chi_square, $dist_t,
// and $dist_erlang. Their runtime behavior depends on how the seed is produced:
// §20.14.2 makes the seed an inout argument (a value is passed in and a
// different value comes back) and requires each function to return the same
// value for the same seed. These tests therefore build the seed from a real
// declared-and-assigned integral variable and drive the module through the full
// pipeline (parse → elaborate → lower → run), reading results back through
// $display, rather than hand-building a system-call node and calling the
// evaluator in isolation.
#include <sstream>
#include <string>
#include <vector>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// Runs a single-module source through elaboration and simulation while
// capturing everything the run writes to stdout.
std::string RunCapture(const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  return captured.str();
}

// Splits captured stdout into its non-empty lines.
std::vector<std::string> Lines(const std::string& out) {
  std::vector<std::string> lines;
  std::istringstream in(out);
  std::string line;
  while (std::getline(in, line)) {
    if (!line.empty()) lines.push_back(line);
  }
  return lines;
}

// Parses each captured line as a signed integer.
std::vector<long long> Values(const std::string& out) {
  std::vector<long long> vals;
  for (const auto& line : Lines(out)) vals.push_back(std::stoll(line));
  return vals;
}

// Wraps a procedural body in a module with a seeded integral variable and runs
// it through the full pipeline, returning the number of warnings the run
// produced. Used to observe the positivity diagnostics of §20.14.2.
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

// §20.14.2: all arguments to the distribution functions are integer values and
// each function returns an integer. Driven from source, each of the seven forms
// assigns into an `integer` sink and prints a plain integer with %0d — no
// fractional part, confirming the result is an integer rather than a real.
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
    EXPECT_EQ(line.find('.'), std::string::npos) << line;  // no fractional part
    EXPECT_NO_THROW(std::stoll(line)) << line;
  }
}

// §20.14.2: $dist_uniform returns numbers uniformly distributed in the interval
// bounded by its start and end arguments, so every draw lands within
// [start, end]. The seed is a real declared variable advanced by each call.
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

// §20.14.2: the start and end arguments are integer inputs that bound the
// returned values. They need not be literals — supplied from real declared
// integral variables and driven through the full pipeline, the draws still land
// within [start, end], confirming the bounds are read as integer operands
// however they are produced.
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

// §20.14.2: a distribution function is an expression that yields an integer, so
// it can stand directly as a task-call argument rather than only on the
// right-hand side of an assignment. Used as a $display argument its bounded
// draw still lands within [start, end].
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

// §20.14.2 (shall): a distribution function shall always return the same value
// given the same seed. Re-asserting the same seed value into the inout seed
// variable mid-run replays the identical sequence.
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
  EXPECT_EQ(lines[0], lines[2]);  // first draw of each seeded run matches
  EXPECT_EQ(lines[1], lines[3]);  // second draw matches too
}

// §20.14.2: the seed is an inout argument — a value is passed in and a
// different value is returned. Reading the real seed variable before and after
// a call shows the call wrote an advanced value back through the inout seed.
TEST(DistributionFunctions, SeedIsInoutAndAdvances) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  integer seed;\n"
      "  integer v;\n"
      "  initial begin\n"
      "    seed = 12345;\n"
      "    $display(\"%0d\", seed);\n"  // before the call
      "    v = $dist_uniform(seed, 0, 1000000);\n"
      "    $display(\"%0d\", seed);\n"  // after — advanced by the inout seed
      "  end\n"
      "endmodule\n",
      f);
  auto lines = Lines(out);
  ASSERT_EQ(lines.size(), 2u);
  EXPECT_NE(lines[0], lines[1]);
}

// §20.14.2: the seed selects the stream, so two full-pipeline runs that differ
// only in the value assigned to the seed variable produce different output.
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

// §20.14.2 (edge): when $dist_uniform's start equals its end the bounding
// interval is a single point, so every draw returns that value.
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

// §20.14.2 (shall): the mean argument shall be greater than 0 for $dist_
// exponential; a non-positive mean is reported and a positive mean is not.
TEST(DistributionFunctions, ExponentialMeanPositivity) {
  EXPECT_GE(WarnCount("    v = $dist_exponential(seed, 0);\n"), 1u);
  EXPECT_EQ(WarnCount("    v = $dist_exponential(seed, 5);\n"), 0u);
}

// §20.14.2 (shall): $dist_poisson also takes a mean that shall be greater
// than 0.
TEST(DistributionFunctions, PoissonMeanPositivity) {
  EXPECT_GE(WarnCount("    v = $dist_poisson(seed, 0);\n"), 1u);
  EXPECT_EQ(WarnCount("    v = $dist_poisson(seed, 10);\n"), 0u);
}

// §20.14.2: the positivity requirement names exponential, poisson, chi-square,
// t, and erlang — not $dist_normal, whose mean may be zero or negative, so it
// draws without complaint.
TEST(DistributionFunctions, NormalAllowsNonPositiveMean) {
  EXPECT_EQ(WarnCount("    v = $dist_normal(seed, 0, 4);\n"), 0u);
}

// §20.14.2 (shall): the degree_of_freedom argument of $dist_chi_square and
// $dist_t shall be greater than 0.
TEST(DistributionFunctions, DegreeOfFreedomPositivity) {
  EXPECT_GE(WarnCount("    v = $dist_chi_square(seed, 0);\n"), 1u);
  EXPECT_EQ(WarnCount("    v = $dist_chi_square(seed, 3);\n"), 0u);
  EXPECT_GE(WarnCount("    v = $dist_t(seed, 0);\n"), 1u);
  EXPECT_EQ(WarnCount("    v = $dist_t(seed, 4);\n"), 0u);
}

// §20.14.2 (shall): for $dist_erlang both k_stage and mean shall be greater
// than 0, so a non-positive value of either is reported while two positive
// arguments draw silently.
TEST(DistributionFunctions, ErlangKStageAndMeanPositivity) {
  EXPECT_GE(WarnCount("    v = $dist_erlang(seed, 0, 7);\n"), 1u);
  EXPECT_GE(WarnCount("    v = $dist_erlang(seed, 2, 0);\n"), 1u);
  EXPECT_EQ(WarnCount("    v = $dist_erlang(seed, 2, 7);\n"), 0u);
}

// §20.14.2 (shall, edge): the positivity check treats the argument as a signed
// integer, so a negative mean — not only zero — is reported. The negative value
// comes from a real declared-and-assigned integral variable.
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

}  // namespace
