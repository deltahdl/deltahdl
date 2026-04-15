#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

namespace {

TEST(ParameterizedModules, ParameterizedModuleSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module m #(parameter int W = 4)(\n"
      "  input logic [W-1:0] a,\n"
      "  output logic [W-1:0] y);\n"
      "  assign y = ~a;\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
