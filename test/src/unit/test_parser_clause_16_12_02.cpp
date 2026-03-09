#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA210, PropertyExpr_SequenceExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##1 b);\n"
              "endmodule\n"));
}

TEST(ParserA210, PropertyExpr_Strong) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) strong(a ##1 b));\n"
              "endmodule\n"));
}

TEST(ParserA210, PropertyExpr_Weak) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) weak(a ##1 b));\n"
              "endmodule\n"));
}

TEST(ParserSection16, Sec16_5_1_StrongSequence) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) strong(a ##1 b ##1 c));\n"
              "endmodule\n"));
}

TEST(ParserSection16, Sec16_5_1_WeakSequence) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) weak(a ##1 b));\n"
              "endmodule\n"));
}

TEST(ParserSection16, StrongSequenceProperty) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) strong(a ##1 b ##1 c));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, WeakSequenceProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) weak(a ##1 b));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

}  // namespace
