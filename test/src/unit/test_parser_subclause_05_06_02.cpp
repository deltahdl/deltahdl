#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(LexicalConventionParsing, KeywordsAreReserved) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire w;\n"
              "  logic l;\n"
              "  assign w = 0;\n"
              "  initial begin\n"
              "    if (l) w = 1;\n"
              "    else w = 0;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, UppercaseNotKeyword) {
  auto r = Parse("MODULE m; endmodule");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected top-level declaration", 1, "3.12.1"));
}

TEST(LexicalConventionParsing, EscapedKeywordNotInterpretedAsKeyword) {
  EXPECT_TRUE(ParseOk("module m; logic \\begin ; endmodule"));
}

TEST(LexicalConventionParsing, AllUppercaseUsedAsIdentifier) {
  EXPECT_TRUE(ParseOk("module m; logic MODULE; endmodule"));
}

}  // namespace
