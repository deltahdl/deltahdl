// §11.4.11: Conditional operator

#include <gtest/gtest.h>

#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"
#include "fixture_synthesizer.h"

using namespace delta;

namespace {

TEST(SynthLower, AssignTernaryMux) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input sel, input a, input b, output y);\n"
                           "  assign y = sel ? a : b;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 3);
  EXPECT_EQ(aig->outputs.size(), 1);
}

}  // namespace
