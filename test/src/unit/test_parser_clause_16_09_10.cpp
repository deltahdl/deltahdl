// §16.9.10: Sequence contained within another sequence

#include "fixture_parser.h"

using namespace delta;


namespace {

// sequence_expr ::= sequence_expr within sequence_expr
TEST(ParserA210, SequenceExpr_Within) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    (a ##1 b) within (c ##[1:5] d));\n"
              "endmodule\n"));
}

}  // namespace
