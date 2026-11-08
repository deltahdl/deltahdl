#include <gtest/gtest.h>

#include <set>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_text_lines.h"

using namespace delta;

namespace {

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
  bool saw_wide = false;
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
  EXPECT_EQ(lines[0], lines[2]);
  EXPECT_EQ(lines[1], lines[3]);
}

TEST(RandomSim, TheSeedIsWrittenBackToAPropertyAndAQueueElement) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C;\n"
                       "  int seed = 99;\n"
                       "  static int sseed = 99;\n"
                       "  function int draw();\n"
                       "    return $random(seed);\n"
                       "  endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  C c = new;\n"
                       "  int a, b, d, e, s = 99;\n"
                       "  int qm[$] = '{99};\n"
                       "  initial begin\n"
                       "    a = c.draw();\n"
                       "    b = $random(C::sseed);\n"
                       "    d = $random(qm[0]);\n"
                       "    e = $random(s);\n"
                       "    $display(\"%0d %0d %0d %0d %0d %0d\", a == e, "
                       "b == e, d == e, c.seed == s, C::sseed == s, "
                       "qm[0] == s && s != 99);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 1 1 1 1 1\n");
}

}  // namespace
