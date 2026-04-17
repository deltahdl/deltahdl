#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

namespace {

// Synthesis accepts upward reference to a parameter in the enclosing module.

TEST(UpwardNameReferenceSynthesis, UpwardParameterReferenceSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module child(input logic [7:0] a, output logic [7:0] y);\n"
      "  assign y = a & parent.MASK;\n"
      "endmodule\n"
      "module parent(input logic [7:0] a, output logic [7:0] y);\n"
      "  parameter logic [7:0] MASK = 8'hF0;\n"
      "  child c1(.a(a), .y(y));\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

// Synthesis accepts upward reference to a net in the enclosing module.

TEST(UpwardNameReferenceSynthesis, UpwardNetReferenceSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module child(output logic y);\n"
      "  assign y = parent.src;\n"
      "endmodule\n"
      "module parent(input logic s, output logic y);\n"
      "  wire src;\n"
      "  assign src = s;\n"
      "  child c1(.y(y));\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
