// §16.12.3: Negation property

#include "fixture_parser.h"

using namespace delta;

namespace {

// property_expr ::= not property_expr
TEST(ParserA210, PropertyExpr_Not) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) not a);\n"
              "endmodule\n"));
}

using VerifyParseTest = ProgramTestParse;

// =============================================================================
// Section 16.5.1 -- Property operators in concurrent assertions
// =============================================================================
// Assert property with not (property negation).
TEST(ParserSection16, Sec16_5_1_PropertyNot) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) not (a ##1 b));\n"
              "endmodule\n"));
}

}  // namespace
