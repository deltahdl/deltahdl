#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// This file covers the cast §6.24.1 defines, written on the right-hand side of
// a continuous assignment, which `SynthLower::LowerExprBit` in
// src/synthesizer/synth_lower.cpp has no lowering for.

// The case fails on a run that answers a netlist for this module. The
// right-hand side reaches `SynthLower::LowerExprBit` in
// src/synthesizer/synth_lower.cpp as an `ExprKind::kCast`, and that function
// builds no node for the kind. A design that wrote the cast got a netlist
// contributing constant zero at every bit of the expression while the run
// reported success. §6.24.1 gives the size cast the width its constant
// expression names, which is the eight bits the target declares.
TEST(CastSynthesis, SizeCastIsReportedRatherThanLoweredToZero) {
  SynthFixture f;
  const auto* mod =
      ElaborateSrc(f,
                   "module m(input [3:0] a, output logic [7:0] y);\n"
                   "  assign y = 8'(a);\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "a cast has no lowering", 2,
                            "6.24.1"));
}

}  // namespace
