
#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

namespace {

// --- R1/R4: Port connections with assignment-compatible types shall be
//     accepted ---

TEST(PortConnectionRulesSynthesis, DifferentWidthPortConnectionSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module child(input logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top(input logic [3:0] x, output logic [7:0] y);\n"
      "  child c1(.a(x), .b(y));\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
