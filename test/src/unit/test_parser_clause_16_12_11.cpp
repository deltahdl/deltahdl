#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(AssertionDeclParsing, PropertyExpr_Always) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) always a);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyExpr_AlwaysRange) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) always [0:5] a);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyExpr_SAlways) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) s_always [0:$] a);\n"
              "endmodule\n"));
}

}  // namespace
