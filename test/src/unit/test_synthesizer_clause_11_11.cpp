#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

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
