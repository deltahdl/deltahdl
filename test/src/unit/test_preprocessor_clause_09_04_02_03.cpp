#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(ConditionalEventIffPreprocessor, IffEventControlSurvives) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  always @(posedge clk iff en) q <= d;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("iff"), std::string::npos);
}

TEST(ConditionalEventIffPreprocessor, IffWithEqualitySurvives) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  always @(a iff enable == 1) y <= a;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("iff"), std::string::npos);
  EXPECT_NE(result.find("enable"), std::string::npos);
}

TEST(ConditionalEventIffPreprocessor, MacroInIffCondition) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define GUARD (a && b)\n"
      "module m;\n"
      "  always @(posedge clk iff `GUARD) q <= d;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("a && b"), std::string::npos);
}

TEST(ConditionalEventIffPreprocessor, MacroExpandsToIffEvent) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define SENS @(posedge clk iff en)\n"
      "module m;\n"
      "  always `SENS q <= d;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConditionalEventIffPreprocessor, IfdefAroundIffBody) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define USE_IFF\n"
      "module m;\n"
      "`ifdef USE_IFF\n"
      "  always @(posedge clk iff en) q <= d;\n"
      "`else\n"
      "  always @(posedge clk) q <= d;\n"
      "`endif\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("iff"), std::string::npos);
}

TEST(ConditionalEventIffPreprocessor, IffWithOrSurvives) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  always @(posedge clk iff en or negedge rst) q <= d;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("iff"), std::string::npos);
  EXPECT_NE(result.find("or"), std::string::npos);
}

}  // namespace
