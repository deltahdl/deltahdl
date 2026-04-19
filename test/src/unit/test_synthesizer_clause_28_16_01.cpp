#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// §28.16.1 R1: synthesis of a cont-assign whose delay slot holds a
// mintypmax node must lower cleanly — the synth path drops delays but
// must not choke on the kMinTypMax shape itself.
TEST(MinTypMaxSynthesis, DelayIgnoredInContAssign) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module m(input a, output y);\n"
      "  assign #(1:2:3) y = a;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
