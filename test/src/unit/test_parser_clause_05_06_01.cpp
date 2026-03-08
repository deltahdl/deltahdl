#include "fixture_parser.h"

using namespace delta;

namespace {

// --- §5.6.1: escaped identifiers as declaration names ---

TEST(ParserClause05, Cl5_6_1_EscapedIdentifierAsName) {
  EXPECT_TRUE(ParseOk("module t; wire \\bus+index ; endmodule"));
}

TEST(ParserClause05, Cl5_6_1_EscapedKeywordAsIdentifier) {
  EXPECT_TRUE(ParseOk("module t; wire \\module ; endmodule"));
}

TEST(ParserClause05, Cl5_6_1_EscapedIdentBasic) {
  EXPECT_TRUE(ParseOk("module m; wire \\busa+index ; endmodule"));
}

TEST(ParserClause05, Cl5_6_1_EscapedIdentKeyword) {
  EXPECT_TRUE(ParseOk("module m; wire \\net ; endmodule"));
}

TEST(ParserClause05, Cl5_6_1_EscapedIdentSpecialChars) {
  EXPECT_TRUE(ParseOk("module m; wire \\***error-condition*** ; endmodule"));
}

TEST(ParserClause05, Cl5_6_1_EscapedIdentForwardSlash) {
  EXPECT_TRUE(ParseOk("module m; wire \\net1/\\net2 ; endmodule"));
}

TEST(ParserClause05, Cl5_6_1_EscapedIdentBraces) {
  EXPECT_TRUE(ParseOk("module m; wire \\{a,b} ; endmodule"));
}

// --- §5.6.1: escaped identifier in expression context ---

TEST(ParserClause05, Cl5_6_1_EscapedIdentInExpression) {
  auto r = Parse(
      "module m;\n"
      "  logic \\my-signal ;\n"
      "  initial \\my-signal = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- §5.6.1: escaped identifier in let declaration ---

TEST(ParserClause05, Cl5_6_1_EscapedIdentInLetDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let \\my+let = 1;\n"
              "endmodule\n"));
}

}  // namespace
