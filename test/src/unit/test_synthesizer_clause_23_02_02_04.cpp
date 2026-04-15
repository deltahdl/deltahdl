
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

TEST(DefaultPortValueSynthesis, MultipleInputsWithDefaultsSynthesize) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module m(\n"
      "  input logic a = 1'b0,\n"
      "  input logic b = 1'b1,\n"
      "  output logic y\n"
      ");\n"
      "  assign y = a & b;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
