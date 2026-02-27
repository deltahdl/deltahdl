// §9.4.1: Delay control

#include <gtest/gtest.h>

#include "synthesis/synth_lower.h"
#include "fixture_synthesizer.h"

using namespace delta;

namespace {

TEST(SynthLower, RejectDelay) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  reg x;\n"
                           "  always begin #10 x = 1; end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
