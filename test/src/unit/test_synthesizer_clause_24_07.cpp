#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

namespace {

TEST(ProgramControlTasksSynth, ExitInAlwaysCombRejected) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module m;\n"
      "  logic x;\n"
      "  always_comb begin\n"
      "    x = 1'b0;\n"
      "    $exit();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  synth.Lower(mod);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
