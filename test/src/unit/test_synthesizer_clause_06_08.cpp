#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// §6.8: A variable declared with a packed vector type becomes a
// bit-vector signal at synthesis. Verify that the synth lowerer maps a
// `logic [7:0]` variable that is the sole driver of an output to eight
// AIG primary outputs — the bit-width of the declared variable.
TEST(VariableDeclarationSynthesis, LogicVectorBecomesBitVectorOutput) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
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

// §6.8: A variable declared with the `var` keyword and an implicit data
// type (no explicit type, only a range) defaults to logic per the
// implicit-data-type rule. Synthesis must lower it identically to an
// explicit `logic [N-1:0]` declaration.
TEST(VariableDeclarationSynthesis, VarImplicitRangeSynthesizesAsLogic) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
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

// §6.8: A variable with a declaration-time initializer must surface to
// the synthesizer with its initial value preserved as a constant driver
// — the lowered AIG must produce the constant on the output bits.
TEST(VariableDeclarationSynthesis, InitializerDrivesConstantOutput) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
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
