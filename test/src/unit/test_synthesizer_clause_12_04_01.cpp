#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(IfElseIfSynth, IfElseIfChainSynthesizes) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f,
                   "module m(input [1:0] sel, input a, input b, input c,\n"
                   "         output reg y);\n"
                   "  always_comb begin\n"
                   "    if (sel == 2'd0) y = a;\n"
                   "    else if (sel == 2'd1) y = b;\n"
                   "    else y = c;\n"
                   "  end\n"
                   "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs.size(), 1);
}

TEST(IfElseIfSynth, IfElseIfNoFinalElseSynthesizes) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f,
                   "module m(input sel1, input sel2, input [7:0] a, input [7:0] b,\n"
                   "         output reg [7:0] y);\n"
                   "  always_comb begin\n"
                   "    y = 8'd0;\n"
                   "    if (sel1) y = a;\n"
                   "    else if (sel2) y = b;\n"
                   "  end\n"
                   "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs.size(), 8);
}

}  // namespace
