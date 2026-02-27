// §16.9.9: Conditions over sequences

#include "fixture_parser.h"

using namespace delta;

  return nullptr;
}

namespace {

// sequence_expr ::= expression_or_dist throughout sequence_expr
TEST(ParserA210, SequenceExpr_Throughout) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    en throughout (a ##1 b ##1 c));\n"
              "endmodule\n"));
}

}  // namespace
