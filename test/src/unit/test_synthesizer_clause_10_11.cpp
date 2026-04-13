#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(NetAliasSynth, AliasTwoNets) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m(input a, output b);\n"
      "  alias a = b;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(NetAliasSynth, AliasThreeNets) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m(input a, output b, output c);\n"
      "  alias a = b = c;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
