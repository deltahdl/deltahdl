// §9.2.1: Initial procedures

#include <gtest/gtest.h>

#include "synthesizer/synth_lower.h"
#include "fixture_synthesizer.h"

using namespace delta;

namespace {

TEST(SynthLower, RejectInitialBlock) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f, "module m; initial begin end endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
