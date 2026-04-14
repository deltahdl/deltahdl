// §23.2

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

namespace {

// §3.2 Design elements — synthesis of design element building blocks.
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
