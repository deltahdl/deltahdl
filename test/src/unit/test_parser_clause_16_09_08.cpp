// §16.9.8: First_match operation

#include "fixture_parser.h"

using namespace delta;

namespace {

// sequence_expr ::= first_match ( sequence_expr {, sequence_match_item} )
TEST(ParserA210, SequenceExpr_FirstMatch) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    first_match(a ##[1:5] b));\n"
              "endmodule\n"));
}

}  // namespace
