#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(AlwaysCombSynthesis, AlwaysCombSynthesizesToCombLogic) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input a, input b, output logic y);\n"
                           "  always_comb y = a & b;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(aig->outputs.empty());
  EXPECT_TRUE(aig->latches.empty());
}

TEST(AlwaysCombSynthesis, AlwaysCombIfElseNoLatch) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input sel, input a, input b,\n"
                           "         output logic y);\n"
                           "  always_comb begin\n"
                           "    if (sel) y = a;\n"
                           "    else     y = b;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(aig->outputs.empty());
  EXPECT_TRUE(aig->latches.empty());
}

}  // namespace
