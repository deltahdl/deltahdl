// §16.12.2: Sequence property

#include "fixture_parser.h"

using namespace delta;


namespace {

// =============================================================================
// §A.2.10 Production #19: property_expr — many alternatives
// =============================================================================
// property_expr ::= sequence_expr
TEST(ParserA210, PropertyExpr_SequenceExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##1 b);\n"
              "endmodule\n"));
}

// property_expr ::= strong ( sequence_expr )
TEST(ParserA210, PropertyExpr_Strong) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) strong(a ##1 b));\n"
              "endmodule\n"));
}

// property_expr ::= weak ( sequence_expr )
TEST(ParserA210, PropertyExpr_Weak) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) weak(a ##1 b));\n"
              "endmodule\n"));
}

}  // namespace
