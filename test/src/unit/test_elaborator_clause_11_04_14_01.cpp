#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- Branch 1: nested streaming_concatenation as stream_expression ---

TEST(StreamExpressionConcatElaboration, NestedStreamingConcatAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [15:0] b;\n"
      "  initial b = {>> {{<< {a}}, a}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamExpressionConcatElaboration, DeeplyNestedStreamingAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [23:0] b;\n"
      "  initial b = {>> {{>> {{<< {a}}}}, a, a}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// --- Left-to-right concatenation of multiple stream_expressions ---

TEST(StreamExpressionConcatElaboration, MultipleElementsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b, c;\n"
      "  logic [23:0] dst;\n"
      "  initial dst = {>> {a, b, c}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamExpressionConcatElaboration, UnequalWidthElementsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] b;\n"
      "  logic [11:0] dst;\n"
      "  initial dst = {>> {a, b}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamExpressionConcatElaboration, LiteralElementsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] dst;\n"
      "  initial dst = {>> {8'hAB, 8'hCD}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
