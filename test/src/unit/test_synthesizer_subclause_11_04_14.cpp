#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// This file covers the streaming operator §11.4.14 defines, written on the
// right-hand side of a continuous assignment, which
// `SynthLower::LowerExprBit` in src/synthesizer/synth_lower.cpp has no
// lowering for.

// The case fails on a run that answers a netlist for this module. The
// right-hand side reaches `SynthLower::LowerExprBit` in
// src/synthesizer/synth_lower.cpp as an `ExprKind::kStreamingConcat`, and that
// function builds no node for the kind. A design that wrote the operator got a
// netlist contributing constant zero at every bit of the expression while the
// run reported success. §11.4.14 rules that the streaming operator packs its
// operand into a sequence of bits in a user-specified order, so the four bits
// the target declares are the four bits the source reads.
TEST(StreamingConcatenationSynthesis,
     StreamingOperatorIsReportedRatherThanLoweredToZero) {
  SynthFixture f;
  const auto* mod =
      ElaborateSrc(f,
                   "module m(input [3:0] a, output logic [3:0] y);\n"
                   "  assign y = {<<{a}};\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a streaming operator has no lowering", 2,
                            "11.4.14"));
}

}  // namespace
