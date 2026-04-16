#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

namespace {

// --- Req 1: Nested module with explicit instantiation synthesizes ---

TEST(NestedModuleSynthesis, NestedModuleExplicitlyInstantiatedSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module m(input logic a, output logic y);\n"
      "  module inner(input logic a, output logic y);\n"
      "    assign y = ~a;\n"
      "  endmodule\n"
      "  inner i1(.a(a), .y(y));\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

// --- Req 4: Portless nested module implicitly instantiated synthesizes ---

TEST(NestedModuleSynthesis, PortlessNestedModuleImplicitInstantiationSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module m(input logic a, output logic y);\n"
      "  assign y = a;\n"
      "  module inner;\n"
      "    wire w;\n"
      "  endmodule\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

// --- Req 5: Ported nested module not instantiated is ignored ---

TEST(NestedModuleSynthesis, PortedNestedModuleNotInstantiatedSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module m(input logic a, output logic y);\n"
      "  assign y = a;\n"
      "  module unused(input logic x, output logic z);\n"
      "    assign z = x;\n"
      "  endmodule\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
