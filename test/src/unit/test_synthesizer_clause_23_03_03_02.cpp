
#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

namespace {

// --- R2: output port can be connected to a variable ---

TEST(PortConnectionRulesForVariablesSynthesis,
     OutputPortDrivingVariableSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module child(input logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top(input logic [7:0] x, output logic [7:0] y);\n"
      "  child c1(.a(x), .b(y));\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

// --- R3: output port can be connected to a net; multiple drivers permitted ---

TEST(PortConnectionRulesForVariablesSynthesis,
     OutputPortDrivingNetSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module child(output logic y);\n"
      "  assign y = 1'b1;\n"
      "endmodule\n"
      "module top(output wire w);\n"
      "  child c1(.y(w));\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
