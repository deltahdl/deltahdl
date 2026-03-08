#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserClause05, Cl5_6_2_KeywordsAreReserved) {
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

TEST(ParserClause05, Cl5_6_2_UppercaseNotKeyword) {
  EXPECT_FALSE(ParseOk("MODULE m; endmodule"));
}

TEST(ParserClause05, Cl5_6_2_EscapedKeywordAsIdentifier) {
  EXPECT_TRUE(ParseOk("module m; logic \\begin ; endmodule"));
}

}
