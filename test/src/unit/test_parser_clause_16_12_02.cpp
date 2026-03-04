// §16.12.2: Sequence property

#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// §A.2.10 Production #19: property_expr — many alternatives
// =============================================================================
// property_expr ::= sequence_expr
TEST(ParserA210, PropertyExpr_SequenceExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##1 b);\n"
              "endmodule\n"));
}

// property_expr ::= strong ( sequence_expr )
TEST(ParserA210, PropertyExpr_Strong) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) strong(a ##1 b));\n"
              "endmodule\n"));
}

// property_expr ::= weak ( sequence_expr )
TEST(ParserA210, PropertyExpr_Weak) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) weak(a ##1 b));\n"
              "endmodule\n"));
}

// =============================================================================
// Section 16.5.1 -- Strong and weak sequences
// =============================================================================
// Assert property with strong sequence.
TEST(ParserSection16, Sec16_5_1_StrongSequence) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) strong(a ##1 b ##1 c));\n"
              "endmodule\n"));
}

// Assert property with weak sequence.
TEST(ParserSection16, Sec16_5_1_WeakSequence) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) weak(a ##1 b));\n"
              "endmodule\n"));
}

// --- Test helpers ---
// =============================================================================
// §16.14 Concurrent assertions — procedural context
// =============================================================================
// =============================================================================
// §16.14.2 Sequence property — strong/weak
// =============================================================================
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
