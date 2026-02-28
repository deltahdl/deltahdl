// §16.12.12: Until property

#include "fixture_parser.h"

using namespace delta;

return nullptr;
}

namespace {

// property_expr ::= property_expr until property_expr
TEST(ParserA210, PropertyExpr_Until) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a until b);\n"
              "endmodule\n"));
}

// property_expr ::= property_expr s_until property_expr
TEST(ParserA210, PropertyExpr_SUntil) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a s_until b);\n"
              "endmodule\n"));
}

// property_expr ::= property_expr until_with property_expr
TEST(ParserA210, PropertyExpr_UntilWith) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a until_with b);\n"
              "endmodule\n"));
}

// property_expr ::= property_expr s_until_with property_expr
TEST(ParserA210, PropertyExpr_SUntilWith) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a s_until_with b);\n"
              "endmodule\n"));
}

}  // namespace
