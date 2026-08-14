#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// This file covers the minimum, typical, and maximum delay expression §11.11
// defines, written on the right-hand side of a continuous assignment, which
// `SynthLower::LowerExprBit` in src/synthesizer/synth_lower.cpp has no
// lowering for.

// The case fails on a run that answers a netlist for this module. The
// right-hand side reaches `SynthLower::LowerExprBit` in
// src/synthesizer/synth_lower.cpp as an `ExprKind::kMinTypMax`, and that
// function builds no node for the kind. A design that wrote the triplet got a
// netlist contributing constant zero at every bit of the expression while the
// run reported success. §11.11 rules that the triplet may be used wherever an
// expression can appear, and the member it selects is one of the three
// four-bit operands the target's declared width holds.
TEST(MinTypMaxSynthesis, DelayTripletIsReportedRatherThanLoweredToZero) {
  SynthFixture f;
  const auto* mod =
      ElaborateSrc(f,
                   "module m(input [3:0] a, input [3:0] b,\n"
                   "         input [3:0] c, output logic [3:0] y);\n"
                   "  assign y = (a:b:c);\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a minimum, typical, and maximum delay expression has no lowering", 3,
      "11.11"));
}

}  // namespace
