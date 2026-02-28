// §16.9.7: OR operation

#include "fixture_parser.h"

using namespace delta;

namespace {

// sequence_expr ::= sequence_expr or sequence_expr
TEST(ParserA210, SequenceExpr_Or) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a or b);\n"
              "endmodule\n"));
}

}  // namespace
