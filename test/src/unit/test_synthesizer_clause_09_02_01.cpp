#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(InitialProcedureSynthesis, RejectInitialBlock) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f, "module m; initial begin end endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(InitialProcedureSynthesis, RejectInitialWithAssignment) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module m;\n"
      "  logic x;\n"
      "  initial x = 1;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
