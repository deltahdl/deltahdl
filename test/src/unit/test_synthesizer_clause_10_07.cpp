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

  for (size_t i = 4; i < 8; ++i) {
    EXPECT_EQ(aig->outputs[i], AigGraph::kConstFalse);
  }
}

// §10.7: when the right-hand side is signed, extension is sign-extension rather
// than zero-fill. A signed 4-bit input widened to a signed 8-bit output must
// drive the four padded high bits from the source sign bit (output bit 3), not
// from constant zero as the unsigned case above does.
TEST(AssignmentExtensionTruncationSynth, SignedExtensionReplicatesSignBit) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f,
                   "module m(input signed [3:0] a, output signed [7:0] y);\n"
                   "  assign y = a;\n"
                   "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 4);
  EXPECT_EQ(aig->outputs.size(), 8);

  // The sign bit lands at output[3] and must be a genuine input literal, not
  // constant zero; every padded high bit replicates it.
  EXPECT_NE(aig->outputs[3], AigGraph::kConstFalse);
  for (size_t i = 4; i < 8; ++i) {
    EXPECT_EQ(aig->outputs[i], aig->outputs[3]);
  }
}

}  // namespace
