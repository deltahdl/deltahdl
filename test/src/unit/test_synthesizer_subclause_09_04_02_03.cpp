#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(ConditionalEventIffSynthesis, LatchWithIffGuard) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(output logic [31:0] y,\n"
                           "         input [31:0] a, input enable);\n"
                           "  always @(a iff enable == 1)\n"
                           "    y <= a;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(aig->outputs.empty());
  EXPECT_FALSE(aig->latches.empty());
}

TEST(ConditionalEventIffSynthesis, AlwaysFFPosedgeIff) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input clk, input en,\n"
                           "         input [7:0] d, output logic [7:0] q);\n"
                           "  always_ff @(posedge clk iff en)\n"
                           "    q <= d;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(aig->outputs.empty());
}

TEST(ConditionalEventIffSynthesis, IffPrecedenceOverOrSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input clk, input rst, input en,\n"
                           "         input [7:0] d, output logic [7:0] q);\n"
                           "  always @(posedge clk iff en or negedge rst)\n"
                           "    if (!rst) q <= 0;\n"
                           "    else q <= d;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(aig->outputs.empty());
}

}  // namespace
