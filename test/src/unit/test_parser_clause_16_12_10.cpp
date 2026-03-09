#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA210, PropertyExpr_Nexttime) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) nexttime a);\n"
              "endmodule\n"));
}

TEST(ParserA210, PropertyExpr_NexttimeWithCount) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) nexttime [3] a);\n"
              "endmodule\n"));
}

TEST(ParserA210, PropertyExpr_SNexttime) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) s_nexttime a);\n"
              "endmodule\n"));
}

TEST(ParserA210, PropertyExpr_SNexttimeWithCount) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) s_nexttime [2] a);\n"
              "endmodule\n"));
}

}  // namespace
