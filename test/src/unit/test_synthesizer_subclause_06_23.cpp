#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// This file covers the type operator §6.23 defines, written as an operand of a
// comparison on the right-hand side of a continuous assignment, which
// `SynthLower::LowerExprBit` in src/synthesizer/synth_lower.cpp has no
// lowering for.

// §6.23 with §6.22.1: a comparison of two type references is a constant, which
// the elaborator folds to the bit it stands for wherever it can type both
// operands, as it can two ports, an operation on them and a written type. The
// netlist carries those bits: a's type, logic [3:0], matches b's and that of
// a + b, and does not match bit [3:0], a 2-state type.
TEST(TypeOperatorSynthesis, FoldedComparisonLowersToTheBitItStandsFor) {
  SynthFixture f;
  const auto* mod = ElaborateSrc(
      f,
      "module m(input [3:0] a, input [3:0] b, output logic [2:0] y);\n"
      "  assign y = {type(a) == type(b), type(a) == type(bit [3:0]),\n"
      "              type(a + b) == type(logic [3:0])};\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs[2], AigGraph::kConstTrue);
  EXPECT_EQ(aig->outputs[1], AigGraph::kConstFalse);
  EXPECT_EQ(aig->outputs[0], AigGraph::kConstTrue);
}

// The case fails on a run that answers a netlist for this module. The
// elaborator does not type a method call's type reference, so it leaves this
// comparison unfolded, and each operand of the comparison reaches
// `SynthLower::LowerExprBit` in src/synthesizer/synth_lower.cpp as an
// `ExprKind::kTypeRef`, for which that function builds no node. A design that
// wrote the operator got a netlist contributing constant zero at every bit of
// the expression while the run reported success. §6.23 rules that a type
// reference is compared only with another type reference, which is what the
// source writes, and §11.4.5 makes the comparison the one bit the target
// declares.
TEST(TypeOperatorSynthesis, TypeReferenceIsReportedRatherThanLoweredToZero) {
  SynthFixture f;
  const auto* mod = ElaborateSrc(f,
                                 "module m(output logic y);\n"
                                 "  typedef enum logic [1:0] {A, B} e_t;\n"
                                 "  e_t e;\n"
                                 "  assign y = (type(e.next()) == type(e_t));\n"
                                 "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the type operator has no lowering", 4, "6.23"));
}

}  // namespace
