#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "helpers_synth_input_sweep.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(ConditionalStatementSynth, AlwaysCombIfElse) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f,
                   "module m(input sel, input a, input b, output reg y);\n"
                   "  always_comb begin\n"
                   "    if (sel) y = a;\n"
                   "    else y = b;\n"
                   "  end\n"
                   "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 3);
  EXPECT_EQ(aig->outputs.size(), 1);
}

TEST(ConditionalStatementSynth, IfWithoutElseSynthesizes) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f,
                   "module m(input sel, input [7:0] a, output reg [7:0] y);\n"
                   "  always_comb begin\n"
                   "    y = 8'd0;\n"
                   "    if (sel) y = a;\n"
                   "  end\n"
                   "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs.size(), 8);
}

// Every case below fails on a lowering that decides an `if` by bit 0 of its
// condition alone. §12.4 makes the condition true where it has a nonzero known
// value, and gives `if (expression)` as the same logic as `if (expression !=
// 0)`, so every bit of the condition's value takes part.

// The test fails at the seven even nonzero values of `a`, whose bit 0 is zero.
TEST(IfConditionSynthesis, AMultiBitConditionIsTrueWhereItIsNonzero) {
  ExpectInputSweep(
      "module m(input [3:0] a, output logic y);\n"
      "  always_comb begin\n"
      "    if (a) y = 1'b1;\n"
      "    else y = 1'b0;\n"
      "  end\n"
      "endmodule\n",
      16, [](uint64_t a) -> uint64_t { return a != 0 ? 1 : 0; });
}

// The test fails on a lowering that reads the condition at the size of the
// assignments it guards, which the case above passes because its target is
// one bit wide. §12.4 gives the condition no context to size it, so `a << 1`
// is four bits long and drops the bit that leaves the top of `a`: at `a = 8`
// the condition is zero. A lowering that reads bit 0 alone fails at every
// other nonzero `a`, whose shift has bit 0 clear.
TEST(IfConditionSynthesis, TheConditionIsSizedByItself) {
  ExpectInputSweep(
      "module m(input [3:0] a, output logic [7:0] y);\n"
      "  always_comb begin\n"
      "    if (a << 1) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      16,
      [](uint64_t a) -> uint64_t { return ((a << 1) & 0xFu) != 0 ? 1 : 0; });
}

// The test fails on a fix that reads a condition of unknown width across a
// guessed width and reports nothing. Whether a value is nonzero turns on every
// bit it has, so a condition whose width the synthesizer cannot answer is one
// it cannot test. `SynthLower::ExprWidth` reads no function's declaration, so a
// call is such a condition.
TEST(IfConditionSynthesis, AConditionOfUnknownWidthIsReported) {
  SynthFixture f;
  const auto* mod =
      ElaborateSrc(f,
                   "module m(input [3:0] a, output logic y);\n"
                   "  function logic [3:0] g(input logic [3:0] v); return v; "
                   "endfunction\n"
                   "  always_comb begin\n"
                   "    if (g(a)) y = 1'b1;\n"
                   "    else y = 1'b0;\n"
                   "  end\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operand has no width in the synthesizer", 4,
                            "12.4"));
}

}  // namespace
