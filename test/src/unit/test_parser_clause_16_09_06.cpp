// §16.9.6: Intersection (AND with length restriction)

#include "fixture_parser.h"

using namespace delta;

  return nullptr;
}

namespace {

// sequence_expr ::= sequence_expr intersect sequence_expr
TEST(ParserA210, SequenceExpr_Intersect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    (a ##1 b) intersect (c ##1 d));\n"
              "endmodule\n"));
}

}  // namespace
