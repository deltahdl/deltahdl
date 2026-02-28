// §16.12.9: Followed-by property

#include "fixture_parser.h"

using namespace delta;

namespace {

// property_expr ::= sequence_expr #-# property_expr
TEST(ParserA210, PropertyExpr_FollowedByOverlapped) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a #-# b);\n"
              "endmodule\n"));
}

// property_expr ::= sequence_expr #=# property_expr
TEST(ParserA210, PropertyExpr_FollowedByNonOverlapped) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a #=# b);\n"
              "endmodule\n"));
}

}  // namespace
