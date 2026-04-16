
#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

namespace {

// --- Req 1: Extern declaration shall not interfere with synthesis ---

TEST(ExternModuleSynthesis, ExternDoesNotInterfereWithSynthesis) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "extern module child(input logic a, output logic y);\n"
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

// --- Req 2: .* port resolution from extern synthesizes correctly ---

TEST(ExternModuleSynthesis, WildcardPortsFromExternSynthesize) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "extern module child(input logic a, output logic y);\n"
      "module child(.*);\n"
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
