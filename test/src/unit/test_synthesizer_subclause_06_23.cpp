#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// This file covers the type operator §6.23 defines, written as an operand of a
// comparison on the right-hand side of a continuous assignment, which
// `SynthLower::LowerExprBit` in src/synthesizer/synth_lower.cpp has no
// lowering for.

// The case fails on a run that answers a netlist for this module. Each operand
// of the comparison reaches `SynthLower::LowerExprBit` in
// src/synthesizer/synth_lower.cpp as an `ExprKind::kTypeRef`, and that
// function builds no node for the kind. A design that wrote the operator got a
// netlist contributing constant zero at every bit of the expression while the
// run reported success. §6.23 rules that a type reference is compared only
// with another type reference, which is what the source writes, and §11.4.5
// makes the comparison the one bit the target declares.
TEST(TypeOperatorSynthesis, TypeReferenceIsReportedRatherThanLoweredToZero) {
  SynthFixture f;
  const auto* mod =
      ElaborateSrc(f,
                   "module m(input [3:0] a, input [3:0] b, output logic y);\n"
                   "  assign y = (type(a) == type(b));\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the type operator has no lowering", 2, "6.23"));
}

}  // namespace
