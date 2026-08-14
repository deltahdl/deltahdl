#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// This file covers the real literal §5.7.2 defines, written on the right-hand
// side of a continuous assignment, which `SynthLower::LowerExprBit` in
// src/synthesizer/synth_lower.cpp has no lowering for.

// The case fails on a run that answers a netlist for this module. The
// right-hand side reaches `SynthLower::LowerExprBit` in
// src/synthesizer/synth_lower.cpp as an `ExprKind::kRealLiteral`, and that
// function builds no node for the kind. A design that wrote the literal got a
// netlist contributing constant zero at every bit of the expression while the
// run reported success. §5.7.2 defines the real literal the design wrote, and
// §6.12.1 rules that converting 1.5 to an integer yields 2, so the four bits
// the target declares hold the value the assignment converts the literal to.
TEST(RealLiteralSynthesis, RealLiteralIsReportedRatherThanLoweredToZero) {
  SynthFixture f;
  const auto* mod = ElaborateSrc(f,
                                 "module m(output logic [3:0] x);\n"
                                 "  assign x = 1.5;\n"
                                 "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a real literal constant has no lowering", 2,
                            "5.7.2"));
}

}  // namespace
