#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(AssertionDeclParsing, PropertyExpr_Until) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a until b);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyExpr_SUntil) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a s_until b);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyExpr_UntilWith) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a until_with b);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, PropertyExpr_SUntilWith) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a s_until_with b);\n"
              "endmodule\n"));
}

}  // namespace
