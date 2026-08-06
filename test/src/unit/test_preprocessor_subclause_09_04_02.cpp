#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(EventControlPreprocessor, PosedgeEventControlSurvivesPreprocessor) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  reg clk;\n"
      "  reg q;\n"
      "  always @(posedge clk) q <= 1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("@(posedge clk)"), std::string::npos);
}

TEST(EventControlPreprocessor, NegedgeEventControlSurvivesPreprocessor) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  reg clk;\n"
      "  reg q;\n"
      "  always @(negedge clk) q <= 0;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("@(negedge clk)"), std::string::npos);
}

TEST(EventControlPreprocessor, EdgeEventControlSurvivesPreprocessor) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  reg clk;\n"
      "  reg q;\n"
      "  always @(edge clk) q <= 1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("@(edge clk)"), std::string::npos);
}

TEST(EventControlPreprocessor, BareSignalEventControlSurvivesPreprocessor) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  reg sig;\n"
      "  reg q;\n"
      "  always @(sig) q = sig;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("@(sig)"), std::string::npos);
}

TEST(EventControlPreprocessor, OrEventExpressionSurvivesPreprocessor) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  reg clk_a, rst;\n"
      "  reg q;\n"
      "  always @(posedge clk_a or negedge rst) q <= 0;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("@(posedge clk_a or negedge rst)"), std::string::npos);
}

TEST(EventControlPreprocessor, MacroExpansionInEdgeIdentifier) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define EDGE posedge\n"
      "module m;\n"
      "  reg clk;\n"
      "  reg q;\n"
      "  always @(`EDGE clk) q <= 1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("posedge clk"), std::string::npos);
}

TEST(EventControlPreprocessor, MacroExpansionInNamedEventControl) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define EV my_event\n"
      "module m;\n"
      "  event my_event;\n"
      "  initial @(`EV) ;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("@(my_event)"), std::string::npos);
}

}  // namespace
