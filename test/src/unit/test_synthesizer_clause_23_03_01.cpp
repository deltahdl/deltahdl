// §23.3.1

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

namespace {

TEST(TopLevelModules, SingleTopLevelModuleSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module top(\n"
      "  input logic a,\n"
      "  output logic y);\n"
      "  assign y = a;\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(TopLevelModules, TopLevelWithChildInstanceSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module child(input logic a, output logic y);\n"
      "  assign y = ~a;\n"
      "endmodule\n"
      "module top(input logic a, output logic y);\n"
      "  child c1(.a(a), .y(y));\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
