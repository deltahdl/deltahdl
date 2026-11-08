#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "helpers_synth_input_sweep.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

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
