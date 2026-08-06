#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(SequenceExprElaboration, CycleDelayConcatenationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b, c;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##1 b ##2 c;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SequenceExprElaboration, RangedDelayConcatenationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, req, gnt;\n"
      "  sequence req_gnt;\n"
      "    @(posedge clk) req ##[1:5] gnt;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SequenceExprElaboration, ParenthesizedSequenceWithRepetitionElaborates) {
  // §16.7 `sequence_abbrev` attached to a parenthesized sequence_expr is
  // accepted by the elaborator's downstream walk.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  sequence s;\n"
      "    @(posedge clk) (a ##1 b)[*2];\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SequenceExprElaboration, UnboundedDelayWithDollarElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, req, ack;\n"
      "  property p;\n"
      "    @(posedge clk) req |-> ##[0:$] ack;\n"
      "  endproperty\n"
      "  assert property (p);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
