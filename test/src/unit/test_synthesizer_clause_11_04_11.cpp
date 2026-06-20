#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(SynthLower, AssignTernaryMux) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input sel, input a, input b, output y);\n"
                           "  assign y = sel ? a : b;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 3);
  EXPECT_EQ(aig->outputs.size(), 1);
}

TEST(SynthLower, NestedTernaryMux) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input s1, input s0, input a, input b,\n"
                           "         input c, output y);\n"
                           "  assign y = s1 ? (s0 ? a : b) : c;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 5);
  EXPECT_EQ(aig->outputs.size(), 1);
}

TEST(SynthLower, TernaryMuxWideBus) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m(input sel, input [7:0] a, input [7:0] b, output [7:0] y);\n"
      "  assign y = sel ? a : b;\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs.size(), 8);
}

TEST(SynthLower, ChainedTernaryPriorityMux) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m(input [1:0] sel, input a, input b, input c, output y);\n"
      "  assign y = (sel == 2'd0) ? a : (sel == 2'd1) ? b : c;\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs.size(), 1);
}

}  // namespace
