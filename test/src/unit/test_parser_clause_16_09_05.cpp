// §16.9.5: AND operation

#include "fixture_parser.h"

using namespace delta;

namespace {

// sequence_expr ::= sequence_expr and sequence_expr
TEST(ParserA210, SequenceExpr_And) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a and b);\n"
              "endmodule\n"));
}

}  // namespace
