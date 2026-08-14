#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// This file covers the time literal §5.8 defines, written on the right-hand
// side of a continuous assignment, which `SynthLower::LowerExprBit` in
// src/synthesizer/synth_lower.cpp has no lowering for.

// The case fails on a run that answers a netlist for this module. The
// right-hand side reaches `SynthLower::LowerExprBit` in
// src/synthesizer/synth_lower.cpp as an `ExprKind::kTimeLiteral`, and that
// function builds no node for the kind. A design that wrote the literal got a
// netlist contributing constant zero at every bit of the expression while the
// run reported success. §5.8 writes the time literal as a number followed
// without a space by a time unit, and gives `2.1ns` as an example of one.
// Table 6-8 of §6.11 makes the time type a 64-bit unsigned integer, which is
// the width the target declares.
TEST(TimeLiteralSynthesis, TimeLiteralIsReportedRatherThanLoweredToZero) {
  SynthFixture f;
  const auto* mod = ElaborateSrc(f,
                                 "module m(output logic [63:0] x);\n"
                                 "  assign x = 2.1ns;\n"
                                 "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a time literal has no lowering", 2, "5.8"));
}

}  // namespace
