// §16.12.10: Nexttime property

#include "fixture_parser.h"

using namespace delta;


namespace {

// property_expr ::= nexttime property_expr
TEST(ParserA210, PropertyExpr_Nexttime) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) nexttime a);\n"
              "endmodule\n"));
}

// property_expr ::= nexttime [ constant_expression ] property_expr
TEST(ParserA210, PropertyExpr_NexttimeWithCount) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) nexttime [3] a);\n"
              "endmodule\n"));
}

// property_expr ::= s_nexttime property_expr
TEST(ParserA210, PropertyExpr_SNexttime) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) s_nexttime a);\n"
              "endmodule\n"));
}

// property_expr ::= s_nexttime [ constant_expression ] property_expr
TEST(ParserA210, PropertyExpr_SNexttimeWithCount) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) s_nexttime [2] a);\n"
              "endmodule\n"));
}

}  // namespace
