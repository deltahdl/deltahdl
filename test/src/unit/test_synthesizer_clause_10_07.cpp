#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(AssignmentExtensionTruncationSynth, TruncationReducesOutputWidth) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input [7:0] a, output [3:0] y);\n"
                           "  assign y = a;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 8);
  EXPECT_EQ(aig->outputs.size(), 4);
}

TEST(AssignmentExtensionTruncationSynth, ExtensionIncreasesOutputWidth) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input [3:0] a, output [7:0] y);\n"
                           "  assign y = a;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 4);
  EXPECT_EQ(aig->outputs.size(), 8);
  // Upper 4 bits should be constant false (zero-extended).
  for (size_t i = 4; i < 8; ++i) {
    EXPECT_EQ(aig->outputs[i], AigGraph::kConstFalse);
  }
}

}  // namespace
