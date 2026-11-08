#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

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
