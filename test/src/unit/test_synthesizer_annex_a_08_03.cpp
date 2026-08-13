#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_synthesizer.h"
#include "helpers_aig_eval.h"
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

// A.8.3 lists `++` among the incrementor operators, and §11.4.2 rules that it
// behaves as a blocking assignment, so `++tmp` has to leave the incremented
// bits in the netlist. `ASSERT_NE(aig, nullptr)` and `EXPECT_FALSE(HasErrors)`
// both hold over a graph in which the increment never happened, so the sweep is
// what states the increment took place: it drives every value of `a` through
// the netlist and reads what `y` carries. The width is four bits because at
// width one an increment and a decrement build the same netlist, and the block
// writes `y` itself rather than through `assign y = tmp;` because `Lower`
// lowers `mod->assigns` before `mod->processes` and a continuous assignment
// would read the bits `tmp` held before the block ran. `++tmp` is the prefix
// spelling, which `ParsePrefixExpr` builds as an `ExprKind::kUnary` rather than
// the `ExprKind::kPostfixUnary` that `tmp++` builds.
TEST(ExpressionSynthesis, IncDecCrossLinkInsideAlwaysComb) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input [3:0] a, output logic [3:0] y);\n"
                           "  logic [3:0] tmp;\n"
                           "  always_comb begin\n"
                           "    tmp = a;\n"
                           "    ++tmp;\n"
                           "    y = tmp;\n"
                           "  end\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  for (uint64_t a = 0; a < 16; ++a) {
    EXPECT_EQ(EvalAigOutputs(*aig, a), (a + 1) & 0xFU) << "a = " << a;
  }
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
