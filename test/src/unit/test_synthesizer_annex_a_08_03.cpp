#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(ExpressionSynthesis, BinaryAndExpressionLowers) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f,
                   "module m(input [3:0] a, input [3:0] b, output [3:0] y);\n"
                   "  assign y = a & b;\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ExpressionSynthesis, BinaryOrExpressionLowers) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f,
                   "module m(input [3:0] a, input [3:0] b, output [3:0] y);\n"
                   "  assign y = a | b;\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(ExpressionSynthesis, BinaryXorExpressionLowers) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f,
                   "module m(input [3:0] a, input [3:0] b, output [3:0] y);\n"
                   "  assign y = a ^ b;\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(ExpressionSynthesis, UnaryNotExpressionLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input [3:0] a, output [3:0] y);\n"
                           "  assign y = ~a;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(ExpressionSynthesis, ConditionalExpressionLowersAsMux) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m(input sel, input [3:0] a, input [3:0] b, output [3:0] y);\n"
      "  assign y = sel ? a : b;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ExpressionSynthesis, ConstantExpressionInWidthLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  parameter W = 4 + 4;\n"
                           "  logic [W-1:0] x;\n"
                           "  assign x = 8'hAA;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(ExpressionSynthesis, ConstantRangePartSelectLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input [15:0] data, output [7:0] hi);\n"
                           "  assign hi = data[15:8];\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(ExpressionSynthesis, IndexedRangePlusLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input [15:0] data, output [7:0] lo);\n"
                           "  assign lo = data[0+:8];\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(ExpressionSynthesis, IndexedRangeMinusLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input [15:0] data, output [7:0] hi);\n"
                           "  assign hi = data[15-:8];\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(ExpressionSynthesis, NestedConditionalExpressionLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m(input s1, input s2, input [3:0] a, input [3:0] b,\n"
      "         input [3:0] c, output [3:0] y);\n"
      "  assign y = s1 ? a : (s2 ? b : c);\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(ExpressionSynthesis, IncDecCrossLinkInsideAlwaysComb) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input [3:0] a, output [3:0] y);\n"
                           "  reg [3:0] tmp;\n"
                           "  always_comb begin\n"
                           "    tmp = a;\n"
                           "    ++tmp;\n"
                           "  end\n"
                           "  assign y = tmp;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ExpressionSynthesis, GenvarExpressionDrivesElaboratedLoop) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input [3:0] in, output [3:0] out);\n"
                           "  genvar i;\n"
                           "  for (i = 0; i < 4; i = i + 1) begin : gen\n"
                           "    assign out[i] = in[i];\n"
                           "  end\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
