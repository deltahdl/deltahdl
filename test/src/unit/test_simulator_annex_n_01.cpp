#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_text_lines.h"
#include "simulator/probabilistic_distribution.h"

using namespace delta;

namespace {

TEST(DistributionAlgorithmAnnex, TheAnnexListsTheCodeAndTheSubclauseTheSyntax) {
  EXPECT_EQ(AnnexListingTheDistributionFunctions(), "Annex N");
  EXPECT_EQ(SubclauseDefiningTheDistributionFunctionSyntax(), "20.14");
}

TEST(DistributionAlgorithmAnnex, TheTableCrossListsEachFunctionWithItsCCode) {
  EXPECT_EQ(CFunctionComputing("$dist_uniform"), "rtl_dist_uniform");
  EXPECT_EQ(CFunctionComputing("$dist_normal"), "rtl_dist_normal");
  EXPECT_EQ(CFunctionComputing("$dist_exponential"), "rtl_dist_exponential");
  EXPECT_EQ(CFunctionComputing("$dist_poisson"), "rtl_dist_poisson");
  EXPECT_EQ(CFunctionComputing("$dist_chi_square"), "rtl_dist_chi_square");
  EXPECT_EQ(CFunctionComputing("$dist_t"), "rtl_dist_t");
  EXPECT_EQ(CFunctionComputing("$dist_erlang"), "rtl_dist_erlang");
  EXPECT_EQ(CFunctionComputing("$random"), "rtl_dist_uniform");
  EXPECT_FALSE(CFunctionComputing("$urandom").has_value());
  EXPECT_FALSE(CFunctionComputing("$dist_binomial").has_value());
}

TEST(DistributionAlgorithmAnnex, RandomIsTheUniformDrawOverTheWholeRange) {
  const int32_t kSeeds[] = {0, 1, 12345, -7, INT32_MAX, INT32_MIN};
  for (int32_t s : kSeeds) {
    int32_t uniform_seed = s;
    int32_t uniform = RtlDistUniform(&uniform_seed, INT32_MIN, INT32_MAX);
    int32_t random_seed = s;
    EXPECT_EQ(RtlDistRandom(&random_seed), uniform) << "seed=" << s;
    EXPECT_EQ(random_seed, uniform_seed) << "seed=" << s;
  }
}

TEST(DistributionAlgorithmAnnex, ADesignsRandomIsItsDistUniformOverTheRange) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  integer rs, us, r, u;\n"
      "  initial begin\n"
      "    rs = 12345; us = 12345;\n"
      "    r = $random(rs);\n"
      "    u = $dist_uniform(us, -2147483647 - 1, 2147483647);\n"
      "    $display(\"%0d %0d\", r, u);\n"
      "    $display(\"%0d %0d\", rs, us);\n"
      "    r = $random(rs);\n"
      "    u = $dist_uniform(us, -2147483647 - 1, 2147483647);\n"
      "    $display(\"%0d %0d\", r, u);\n"
      "    $display(\"%0d %0d\", rs, us);\n"
      "  end\n"
      "endmodule\n",
      f);
  auto lines = Lines(out);
  ASSERT_EQ(lines.size(), 4u);
  for (const std::string& line : lines) {
    auto space = line.find(' ');
    ASSERT_NE(space, std::string::npos) << line;
    EXPECT_EQ(line.substr(0, space), line.substr(space + 1)) << line;
  }
  EXPECT_NE(lines[1].substr(0, lines[1].find(' ')), "12345");
  EXPECT_NE(lines[0], lines[2]);
}

TEST(DistributionAlgorithmAnnex, ADesignsRandomAnswersTheReferenceValue) {
  int32_t seed = 777;
  int32_t expected = RtlDistUniform(&seed, INT32_MIN, INT32_MAX);
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  integer seed, v;\n"
      "  initial begin\n"
      "    seed = 777;\n"
      "    v = $random(seed);\n"
      "    $display(\"%0d\", v);\n"
      "    $display(\"%0d\", seed);\n"
      "  end\n"
      "endmodule\n",
      f);
  auto lines = Lines(out);
  ASSERT_EQ(lines.size(), 2u);
  EXPECT_EQ(lines[0], std::to_string(expected));
  EXPECT_EQ(lines[1], std::to_string(seed));
}

}  // namespace
