// §19.5.1.2: Coverpoint bin set covergroup expressions

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA211, BinsOrOptions_SetCovergroupExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins b = x;\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #30: set_covergroup_expression
// =============================================================================
TEST(ParserA211, SetCovergroupExpression) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins b = x;\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

}  // namespace
