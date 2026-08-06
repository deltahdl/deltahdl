#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(SequenceConcatPreprocessor, CycleDelayOperatorSurvives) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  initial @(posedge clk) a ##1 b ##2 c;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("##1"), std::string::npos);
  EXPECT_NE(result.find("##2"), std::string::npos);
}

TEST(SequenceConcatPreprocessor, BracketedDelayRangeSurvives) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ##[1:5] gnt);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("##[1:5]"), std::string::npos);
}

TEST(SequenceConcatPreprocessor, UnboundedDelayRangeWithDollarSurvives) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ##[0:$] ack);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("##[0:$]"), std::string::npos);
}

TEST(SequenceConcatPreprocessor, MacroWithArgExpandsToCycleDelay) {
  // §16.7's cycle_delay_range is just a token sequence to the preprocessor;
  // a function-style macro should substitute its formal into the delay slot.
  PreprocFixture f;
  auto result = Preprocess(
      "`define WAIT(n) ##n\n"
      "module m;\n"
      "  initial @(posedge clk) a `WAIT(4) b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("##4"), std::string::npos);
}

}  // namespace
