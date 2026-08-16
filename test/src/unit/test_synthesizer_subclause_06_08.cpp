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

// The case fails on a run that answers this module anything other than the
// §13.4 report `a function call has no lowering in the synthesizer`, which is
// what the same call draws when it is written on the right of an assignment
// instead: FunctionCallSynthesis.FunctionCallIsReportedRatherThanLoweredToZero
// in test/src/unit/test_synthesizer_subclause_13_04.cpp reads that report off
// `assign q = identity(d);`. §6.8 makes the initializer of a variable
// declaration an expression like any other, so which of the two forms the
// design wrote does not change what the synthesizer can build from
// `identity(d)`, and a design told about one form and not the other gets a
// netlist that drops the call while the run reports success.
//
// Two sites answer for ExprKind::kCall, and the declaration reaches neither
// today. SynthLower::CheckExprSynthesizable at
// src/synthesizer/synth_lower.cpp:14 reports ExprKind::kSystemCall and passes
// over ExprKind::kCall, so SynthLower::CheckDeclSynthesizable at
// src/synthesizer/synth_lower.cpp:304 lets the initializer through.
// SynthLower::LowerExprBit at src/synthesizer/synth_lower.cpp:720 is what
// emits the §13.4 report NonSynthExprRule names, at the SourceLoc the call
// expression starts on, and LowersToNothing at
// src/synthesizer/synth_lower.cpp:823 returns the declaration statement from
// SynthLower::LowerStmt before any bit of the initializer is asked for. This
// is the general case: a kind added to NonSynthExprRule is reported on an
// assignment and silent on a declaration until one of those two sites reaches
// the initializer.
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
                   "    logic [7:0] t = identity(d);\n"
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
