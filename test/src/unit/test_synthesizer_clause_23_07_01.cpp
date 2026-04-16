
#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

namespace {

// --- Requirement 1: :: prefix resolves downward in synthesizable code ---

TEST(ScopeResolutionPrefixSynthesis, PackagePrefixParamSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "package pkg;\n"
      "  parameter int WIDTH = 8;\n"
      "endpackage\n"
      "module t(input logic [pkg::WIDTH-1:0] a,\n"
      "         output logic [pkg::WIDTH-1:0] y);\n"
      "  assign y = a;\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
