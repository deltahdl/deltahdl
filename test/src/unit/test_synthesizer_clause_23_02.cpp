// §23.2

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

namespace {

// §23.2 Module definitions — a minimal empty module reaches the synthesizer
// and lowers to an AIG without diagnostics.
TEST(ModuleDefinitions, MinimalEmpty) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f, "module m; endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(ModuleDefinitions, MacromoduleSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f, "macromodule m; endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
