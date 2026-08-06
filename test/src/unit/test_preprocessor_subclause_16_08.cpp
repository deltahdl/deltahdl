#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(SequenceDeclarationPreprocessor, SequenceBlockSurvives) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  sequence s(input x, input y);\n"
      "    @(posedge clk) x ##1 y;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("sequence s(input x, input y)"), std::string::npos);
  EXPECT_NE(result.find("endsequence"), std::string::npos);
}

TEST(SequenceDeclarationPreprocessor, UntypedKeywordSurvives) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  sequence s(untyped a);\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("untyped"), std::string::npos);
}

TEST(SequenceDeclarationPreprocessor, EndsequenceLabelSurvives) {
  // §16.8 sequence_declaration permits an optional trailing label on
  // `endsequence`; the preprocessor must leave the label tokens intact for
  // the parser to match against the header name.
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence : s\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("endsequence : s"), std::string::npos);
}

TEST(SequenceDeclarationPreprocessor, MacroBodyExpandsToSequence) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define SEQ_BODY @(posedge clk) a ##1 b\n"
      "module m;\n"
      "  sequence s;\n"
      "    `SEQ_BODY;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("a ##1 b"), std::string::npos);
}

}  // namespace
