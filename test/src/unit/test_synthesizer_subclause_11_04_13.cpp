#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "helpers_synth_input_sweep.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// This file covers the set membership operator §11.4.13 defines: written on
// the right-hand side of a continuous assignment, which
// `SynthLower::LowerExprBit` in src/synthesizer/synth_lower.cpp has no
// lowering for, and the value range it matches against, which a §12.5.4
// `case ... inside` item lowers.

// The case fails on a run that answers a netlist for this module. The
// right-hand side reaches `SynthLower::LowerExprBit` in
// src/synthesizer/synth_lower.cpp as an `ExprKind::kInside`, and that function
// builds no node for the kind. A design that wrote the operator got a netlist
// contributing constant zero at every bit of the expression while the run
// reported success. §11.4.13 rules that the operator returns 1'b1 for a match
// and 1'b0 for none, which is the one bit the target declares.
TEST(SetMembershipSynthesis, InsideOperatorIsReportedRatherThanLoweredToZero) {
  SynthFixture f;
  const auto* mod = ElaborateSrc(f,
                                 "module m(input [3:0] a, output logic y);\n"
                                 "  assign y = a inside {1, 2};\n"
                                 "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the set membership operator has no lowering", 2,
                            "11.4.13"));
}

// §11.4.13 matches a value range `[lo:hi]` where the expression is at least
// `lo` and at most `hi`, which are the §11.4.4 comparisons. Those are between
// signed values where every operand is signed, as the selector `a` and the
// unsized decimal bounds `-2` and `2` are (§5.7.1), so the item matches `a`
// from -2 to 2. The test fails on a lowering that reads a bound that is not a
// name as unsigned: there `-2` is a value above `2`, the range holds nothing,
// and `y` is driven to 0 everywhere.
TEST(SetMembershipSynthesis, SignedValueRangeComparesAsSigned) {
  ExpectInputSweep(
      "module m(input signed [3:0] a, output logic y);\n"
      "  always_comb begin\n"
      "    y = 1'b0;\n"
      "    case (a) inside\n"
      "      [-2:2]: y = 1'b1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      16, [](uint64_t a) -> uint64_t {
        int64_t value = static_cast<int64_t>(a) - (a >= 8 ? 16 : 0);
        return value >= -2 && value <= 2 ? 1 : 0;
      });
}

}  // namespace
