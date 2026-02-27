// §16.13.2: Multiclocked properties

#include "fixture_parser.h"

using namespace delta;

  return nullptr;
}

namespace {

// property_expr ::= clocking_event property_expr
TEST(ParserA210, PropertyExpr_ClockingEventPropertyExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (\n"
              "    @(posedge clk) a |-> @(posedge clk2) b);\n"
              "endmodule\n"));
}

}  // namespace
