// §20.14.1 $random — the system function that returns a new 32-bit signed
// random number on each call. Its runtime behavior depends on how its seed is
// produced: §20.14.1 states the seed shall be an integral variable whose value
// is assigned prior to the call, and the seed selects the stream. These tests
// therefore build the seed from a real declared-and-assigned `integer` variable
// and drive the module through the full pipeline (parse → elaborate → lower →
// run), reading back what $random prints through $display rather than
// hand-building a system-call node and calling the evaluator in isolation.
#include <set>
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
  if (design != nullptr) {
    LowerAndRun(design, f);
  }
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

// §20.14.1: $random returns a new number each time it is called, so a stream
// seeded once and then advanced with the seedless form does not stay pinned to
// a single value. The seed is a real declared-and-assigned integral variable,
// as the clause requires.
TEST(RandomFunction, AdvancesAcrossConsecutiveCalls) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  integer seed;\n"
      "  integer v;\n"
      "  initial begin\n"
      "    seed = 12345;\n"
      "    v = $random(seed); $display(\"%0d\", v);\n"
      "    v = $random;       $display(\"%0d\", v);\n"
      "    v = $random;       $display(\"%0d\", v);\n"
      "    v = $random;       $display(\"%0d\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  auto lines = Lines(out);
  ASSERT_EQ(lines.size(), 4u);
  std::set<std::string> distinct(lines.begin(), lines.end());
  EXPECT_GT(distinct.size(), 1u);
}

// §20.14.1: the bare (seedless) form is a complete call in its own right — the
// optional seed is omitted entirely — and it draws from the current stream.
// Called repeatedly with no seed argument at all, it still yields fresh numbers
// that advance rather than repeating a single value.
TEST(RandomFunction, SeedlessFormDrawsAdvancingValues) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  integer v;\n"
      "  initial begin\n"
      "    v = $random; $display(\"%0d\", v);\n"
      "    v = $random; $display(\"%0d\", v);\n"
      "    v = $random; $display(\"%0d\", v);\n"
      "    v = $random; $display(\"%0d\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  auto lines = Lines(out);
  ASSERT_EQ(lines.size(), 4u);
  std::set<std::string> distinct(lines.begin(), lines.end());
  EXPECT_GT(distinct.size(), 1u);
}

// §20.14.1: the random number is a signed integer; it can be positive or
// negative, and it is 32 bits wide. Read back through a signed `integer` sink
// and %0d, a run of draws yields both a negative value (leading '-') and a
// non-negative value — which only holds if the result is interpreted as signed
// — and at least one magnitude that overflows any narrower (<=16-bit) result,
// which only holds if the draw is genuinely a wide 32-bit number.
TEST(RandomFunction, ProducesSignedThirtyTwoBitValues) {
  SimFixture f;
  std::string src =
      "module t;\n"
      "  integer seed;\n"
      "  integer v;\n"
      "  initial begin\n"
      "    seed = 1;\n"
      "    v = $random(seed); $display(\"%0d\", v);\n";
  for (int i = 0; i < 30; ++i) {
    src += "    v = $random; $display(\"%0d\", v);\n";
  }
  src +=
      "  end\n"
      "endmodule\n";
  std::string out = RunCapture(src, f);
  bool saw_negative = false;
  bool saw_nonnegative = false;
  bool saw_wide = false;  // magnitude beyond a 16-bit result's range
  for (const auto& line : Lines(out)) {
    if (line[0] == '-')
      saw_negative = true;
    else
      saw_nonnegative = true;
    long long v = std::stoll(line);
    if (v > 65535 || v < -65536) saw_wide = true;
  }
  EXPECT_TRUE(saw_negative);
  EXPECT_TRUE(saw_nonnegative);
  EXPECT_TRUE(saw_wide);
}

// §20.14.1: the seed argument controls the numbers $random returns, so
// different seeds generate different random streams. Two full-pipeline runs
// that differ only in the value assigned to the seed variable produce different
// output.
TEST(RandomFunction, DifferentSeedsGiveDifferentStreams) {
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
        "    v = $random(seed); $display(\"%0d\", v);\n"
        "    v = $random;       $display(\"%0d\", v);\n"
        "    v = $random;       $display(\"%0d\", v);\n"
        "  end\n"
        "endmodule\n";
    return RunCapture(src, f);
  };
  EXPECT_NE(run_with_seed("1"), run_with_seed("2"));
}

// §20.14.1 (corollary): seeding controls the stream deterministically, so
// re-asserting the same seed mid-run replays the identical sequence. The seed
// value is assigned to the integral variable before each call, exactly as the
// clause prescribes.
TEST(RandomFunction, SameSeedReplaysStream) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  integer seed;\n"
      "  integer a1, a2, b1, b2;\n"
      "  initial begin\n"
      "    seed = 777;\n"
      "    a1 = $random(seed);\n"
      "    a2 = $random;\n"
      "    seed = 777;\n"
      "    b1 = $random(seed);\n"
      "    b2 = $random;\n"
      "    $display(\"%0d\", a1);\n"
      "    $display(\"%0d\", a2);\n"
      "    $display(\"%0d\", b1);\n"
      "    $display(\"%0d\", b2);\n"
      "  end\n"
      "endmodule\n",
      f);
  auto lines = Lines(out);
  ASSERT_EQ(lines.size(), 4u);
  EXPECT_EQ(lines[0], lines[2]);  // first draw of each seeded stream matches
  EXPECT_EQ(lines[1], lines[3]);  // second draw matches too
}

}  // namespace
