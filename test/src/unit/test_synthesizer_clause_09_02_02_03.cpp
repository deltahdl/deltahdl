// §9.2.2.3: Latched logic always_latch procedure

#include <gtest/gtest.h>

#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"
#include "fixture_synthesizer.h"

using namespace delta;

namespace {

TEST(SynthLower, AlwaysLatchCreatesLatch) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input en, input d, output reg q);\n"
                           "  always_latch begin\n"
                           "    if (en) q = d;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs.size(), 1);
  EXPECT_FALSE(aig->latches.empty());
}

}  // namespace
