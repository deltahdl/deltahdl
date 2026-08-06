#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(NonblockingAssignSynthesis, InAlwaysFF) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input clk, input d, output reg q);\n"
                           "  always_ff @(posedge clk)\n"
                           "    q <= d;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(aig->latches.empty());
}

TEST(NonblockingAssignSynthesis, SwapPattern) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input clk, input a_in, input b_in,\n"
                           "         output reg a_out, output reg b_out);\n"
                           "  always_ff @(posedge clk) begin\n"
                           "    a_out <= b_in;\n"
                           "    b_out <= a_in;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_GE(aig->latches.size(), 2u);
}

}  // namespace
