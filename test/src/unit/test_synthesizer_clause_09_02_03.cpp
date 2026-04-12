#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(FinalProcedureSynthesis, RejectFinalBlock) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f, "module m; final begin end endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(FinalProcedureSynthesis, RejectFinalWithAssignment) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module m;\n"
      "  logic x;\n"
      "  final x = 1;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(FinalProcedureSynthesis, RejectFinalWithDisplay) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
      "module m;\n"
      "  final $display(\"done\");\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
