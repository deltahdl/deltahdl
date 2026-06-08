
#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

namespace {

TEST(DefaultPortValueSynthesis, InputPortWithDefaultSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module m(input logic a = 1'b0, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}
