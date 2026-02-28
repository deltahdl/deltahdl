// §16.12.6: If-else property

#include "fixture_parser.h"

using namespace delta;

return nullptr;
}

namespace {

// property_expr ::= if (...) property_expr [else property_expr]
TEST(ParserA210, PropertyExpr_IfElse) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    if (mode) a |-> b else c |-> d);\n"
              "endmodule\n"));
}

TEST(ParserA210, PropertyExpr_IfNoElse) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    if (mode) a |-> b);\n"
              "endmodule\n"));
}

}  // namespace
