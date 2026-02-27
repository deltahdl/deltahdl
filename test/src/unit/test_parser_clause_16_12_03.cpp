// §16.12.3: Negation property

#include "fixture_parser.h"

using namespace delta;

  return nullptr;
}

namespace {

// property_expr ::= not property_expr
TEST(ParserA210, PropertyExpr_Not) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) not a);\n"
              "endmodule\n"));
}

}  // namespace
