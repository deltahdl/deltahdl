#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA210, PropertyExpr_FollowedByOverlapped) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a #-# b);\n"
              "endmodule\n"));
}

TEST(ParserA210, PropertyExpr_FollowedByNonOverlapped) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a #=# b);\n"
              "endmodule\n"));
}

}
