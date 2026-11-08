#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
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

TEST(VariableDeclarationSynthesis,
     DeclInitializerFunctionCallIsReportedUnlowered) {
  SynthFixture f;
  const auto* mod =
      ElaborateSrc(f,
                   "module m(input logic [7:0] d, output logic [7:0] q);\n"
                   "  function logic [7:0] identity(input logic [7:0] v);\n"
                   "    return v;\n"
                   "  endfunction\n"
                   "  always_comb begin\n"
                   "    static logic [7:0] t = identity(d);\n"
                   "    q = t;\n"
                   "  end\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  synth.Lower(mod);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a function call has no lowering in the "
                            "synthesizer",
                            6, "13.4"));
}

}  // namespace
