#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(LevelSensitiveSequencePreprocessor, MacroExpansionInSequenceName) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define SEQ abc\n"
      "module m;\n"
      "  sequence abc;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  initial wait(`SEQ.triggered);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(LevelSensitiveSequencePreprocessor, MacroExpansionInWaitBody) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define DONE_MSG $display(\"done\")\n"
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  initial begin\n"
      "    wait(s.triggered);\n"
      "    `DONE_MSG;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(LevelSensitiveSequencePreprocessor, WaitTriggeredSurvivesPreprocessor) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  sequence abc;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  initial wait(abc.triggered);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("wait"), std::string::npos);
  EXPECT_NE(result.find("triggered"), std::string::npos);
}

}  // namespace
