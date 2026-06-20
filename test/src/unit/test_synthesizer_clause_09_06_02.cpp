#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(DisableStatementSynthesis, RejectDisableInAlwaysComb) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input clk, input rst,\n"
                           "         output logic q);\n"
                           "  always_comb begin : blk\n"
                           "    q = 0;\n"
                           "    if (rst) disable blk;\n"
                           "    q = 1;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(DisableStatementSynthesis, RejectDisableInAlwaysFF) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input clk, input rst,\n"
                           "         output logic q);\n"
                           "  always_ff @(posedge clk) begin : blk\n"
                           "    if (rst) disable blk;\n"
                           "    q <= 1;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
