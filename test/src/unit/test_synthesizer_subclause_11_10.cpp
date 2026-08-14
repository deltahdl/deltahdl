#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// This file covers the string literal §11.10 defines, written on the
// right-hand side of a continuous assignment, which
// `SynthLower::LowerExprBit` in src/synthesizer/synth_lower.cpp has no
// lowering for.

// The case fails on a run that answers a netlist for this module. The
// right-hand side reaches `SynthLower::LowerExprBit` in
// src/synthesizer/synth_lower.cpp as an `ExprKind::kStringLiteral`, and that
// function builds no node for the kind. A design that wrote the literal got a
// netlist contributing constant zero at every bit of the expression while the
// run reported success. §11.10 rules that a string literal operand is a
// sequence of 8-bit ASCII codes, one per character, so the two characters
// written here are the sixteen bits the target declares.
TEST(StringLiteralSynthesis, StringLiteralIsReportedRatherThanLoweredToZero) {
  SynthFixture f;
  const auto* mod = ElaborateSrc(f,
                                 "module m(output logic [15:0] x);\n"
                                 "  assign x = \"ab\";\n"
                                 "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a string literal expression has no lowering", 2,
                            "11.10"));
}

}  // namespace
