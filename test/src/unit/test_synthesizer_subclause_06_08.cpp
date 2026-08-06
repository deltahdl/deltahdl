#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(VariableDeclarationSynthesis, LogicVectorBecomesBitVectorOutput) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(output logic [7:0] y);\n"
                           "  logic [7:0] data;\n"
                           "  assign data = 8'hA5;\n"
                           "  assign y = data;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs.size(), 8u);
}

TEST(VariableDeclarationSynthesis, VarImplicitRangeSynthesizesAsLogic) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(output logic [3:0] y);\n"
                           "  var [3:0] nibble;\n"
                           "  assign nibble = 4'b1010;\n"
                           "  assign y = nibble;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs.size(), 4u);
}

TEST(VariableDeclarationSynthesis, InitializerDrivesConstantOutput) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(output logic [3:0] y);\n"
                           "  logic [3:0] data = 4'b1100;\n"
                           "  assign y = data;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs.size(), 4u);
}

}  // namespace
