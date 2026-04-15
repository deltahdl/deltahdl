
#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

namespace {

TEST(WildcardPortConnectionSynthesis, WildcardConnectionSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module child(input logic a, output logic y);\n"
      "  assign y = ~a;\n"
      "endmodule\n"
      "module top(input logic a, output logic y);\n"
      "  child c1(.*);\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(WildcardPortConnectionSynthesis, WildcardWithNamedOverrideSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module child(input logic a, input logic b, output logic y);\n"
      "  assign y = a & b;\n"
      "endmodule\n"
      "module top(input logic a, input logic x, output logic y);\n"
      "  child c1(.b(x), .*);\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
