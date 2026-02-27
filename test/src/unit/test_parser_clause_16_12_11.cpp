// §16.12.11: Always property

#include "fixture_parser.h"

using namespace delta;

  return nullptr;
}

namespace {

// property_expr ::= always property_expr
TEST(ParserA210, PropertyExpr_Always) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) always a);\n"
              "endmodule\n"));
}

// property_expr ::= always [ cycle_delay_const_range_expression ] property_expr
TEST(ParserA210, PropertyExpr_AlwaysRange) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) always [0:5] a);\n"
              "endmodule\n"));
}

// property_expr ::= s_always [ constant_range ] property_expr
TEST(ParserA210, PropertyExpr_SAlways) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) s_always [0:$] a);\n"
              "endmodule\n"));
}

}  // namespace
