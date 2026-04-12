#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(ImplicitEventSynthesis, AlwaysStarCombLogic) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input a, input b, output logic y);\n"
                           "  always @* y = a & b;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(aig->outputs.empty());
  EXPECT_TRUE(aig->latches.empty());
}

TEST(ImplicitEventSynthesis, AlwaysStarParenCombLogic) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input a, input b, output logic y);\n"
                           "  always @(*) y = a | b;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(aig->outputs.empty());
  EXPECT_TRUE(aig->latches.empty());
}

TEST(ImplicitEventSynthesis, AlwaysStarIfElseNoLatch) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input sel, input a, input b,\n"
                           "         output logic y);\n"
                           "  always @* begin\n"
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

TEST(ImplicitEventSynthesis, AlwaysStarCaseNoLatch) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input [1:0] sel,\n"
                           "         output logic [7:0] y);\n"
                           "  always @* begin\n"
                           "    case (sel)\n"
                           "      2'b00: y = 8'h10;\n"
                           "      2'b01: y = 8'h20;\n"
                           "      2'b10: y = 8'h30;\n"
                           "      default: y = 8'hFF;\n"
                           "    endcase\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(aig->outputs.empty());
  EXPECT_TRUE(aig->latches.empty());
}

TEST(ImplicitEventSynthesis, AlwaysStarMultipleOutputs) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input [7:0] a, input [7:0] b,\n"
                           "         output logic [7:0] sum,\n"
                           "         output logic [7:0] diff);\n"
                           "  always @(*) begin\n"
                           "    sum = a + b;\n"
                           "    diff = a - b;\n"
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
