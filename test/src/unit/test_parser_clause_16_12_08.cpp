// §16.12.8: Implies and iff properties

#include "fixture_parser.h"

using namespace delta;

namespace {

// property_expr ::= property_expr implies property_expr
TEST(ParserA210, PropertyExpr_Implies) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a implies b);\n"
              "endmodule\n"));
}

// property_expr ::= property_expr iff property_expr
TEST(ParserA210, PropertyExpr_Iff) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a iff b);\n"
              "endmodule\n"));
}

}  // namespace
