// Non-LRM tests

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

namespace {

TEST(DesignElementSynth, ModuleWithMultiplePorts) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module m(input a, input b, output y);\n"
      "  assign y = a & b;\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 2);
  EXPECT_EQ(aig->outputs.size(), 1);
}

TEST(DesignElementSynth, RejectInitialBlock) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f, "module m; initial begin end endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
