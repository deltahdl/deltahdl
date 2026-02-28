// §16.12.13: Eventually property

#include "fixture_parser.h"

using namespace delta;

return nullptr;
}

namespace {

// property_expr ::= s_eventually property_expr
TEST(ParserA210, PropertyExpr_SEventually) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) s_eventually a);\n"
              "endmodule\n"));
}

// property_expr ::= s_eventually [ cycle_delay_const_range_expression ]
// property_expr
TEST(ParserA210, PropertyExpr_SEventuallyRange) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) s_eventually [1:5] a);\n"
              "endmodule\n"));
}

// property_expr ::= eventually [ constant_range ] property_expr
TEST(ParserA210, PropertyExpr_Eventually) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) eventually [1:5] a);\n"
              "endmodule\n"));
}

}  // namespace
