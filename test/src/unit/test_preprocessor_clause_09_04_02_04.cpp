#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(SequenceEventPreprocessor, SequenceEventSurvivesPreprocessing) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  sequence abc;\n"
      "    @(posedge clk) a ##1 b ##1 c;\n"
      "  endsequence\n"
      "  initial @(abc) $display(\"matched\");\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("sequence"), std::string::npos);
  EXPECT_NE(result.find("endsequence"), std::string::npos);
  EXPECT_NE(result.find("@(abc)"), std::string::npos);
}

TEST(SequenceEventPreprocessor, MacroExpandsToSequenceEvent) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define WAIT_SEQ @(abc)\n"
      "module m;\n"
      "  sequence abc;\n"
      "    @(posedge clk) a ##1 b ##1 c;\n"
      "  endsequence\n"
      "  initial `WAIT_SEQ $display(\"matched\");\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(SequenceEventPreprocessor, IfdefAroundSequenceEvent) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define USE_SEQ\n"
      "module m;\n"
      "  sequence abc;\n"
      "    @(posedge clk) a ##1 b ##1 c;\n"
      "  endsequence\n"
      "`ifdef USE_SEQ\n"
      "  initial @(abc) $display(\"matched\");\n"
      "`else\n"
      "  initial #1 $display(\"no sequence\");\n"
      "`endif\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("@(abc)"), std::string::npos);
}

}  // namespace
