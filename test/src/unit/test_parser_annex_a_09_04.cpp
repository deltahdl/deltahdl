#include <gtest/gtest.h>

#include "fixture_parser.h"

namespace {

TEST(WhiteSpaceParsing, SpaceDelimiterParses) {
  EXPECT_TRUE(ParseOk("module t; logic a; assign a = 1'b0; endmodule"));
}

TEST(WhiteSpaceParsing, TabDelimiterParses) {
  EXPECT_TRUE(ParseOk("module\tt;\tlogic\ta;\tassign\ta=1'b0;\tendmodule"));
}

TEST(WhiteSpaceParsing, NewlineDelimiterParses) {
  EXPECT_TRUE(
      ParseOk("module\nt\n;\nlogic\na\n;\nassign\na\n=\n1'b0\n;\nendmodule\n"));
}

TEST(WhiteSpaceParsing, FormfeedDelimiterParses) {
  EXPECT_TRUE(ParseOk("module\ft\f;\flogic\fa\f;\fassign\fa=1'b0;\fendmodule"));
}

TEST(WhiteSpaceParsing, EmptyInputParsesEmptyCompilationUnit) {
  auto result = Parse("");
  EXPECT_FALSE(result.has_errors);
  ASSERT_NE(result.cu, nullptr);
}

}  // namespace
