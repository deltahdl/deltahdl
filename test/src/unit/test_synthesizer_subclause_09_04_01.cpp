#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(SynthLower, RejectDelay) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  reg x;\n"
                           "  always begin #10 x = 1; end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "delay control is not synthesizable", 3, "9.4.1"));
}

TEST(SynthLower, DelayInsideInitialProcedureDrawsTheProcedureReport) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  reg x;\n"
                           "  initial #5 x = 1;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "initial procedure is not synthesizable", 3,
                            "9.2.1"));
  EXPECT_EQ(FindDiag(f, "delay control is not synthesizable"), nullptr);
}

TEST(SynthLower, DelayControlIsRejectedByName) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  reg x;\n"
                           "  always begin\n"
                           "    #10 x = 1;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "delay control is not synthesizable", 4, "9.4.1"));
}

TEST(SynthLower, RejectedConstructIsReportedAtItsOwnLocation) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic ready;\n"
                           "  reg x;\n"
                           "  always begin\n"
                           "    wait(ready) x = 1;\n"
                           "    #10 x = 0;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "wait statement is not synthesizable", 5, "9.4.3"));
  EXPECT_EQ(FindDiag(f, "delay control is not synthesizable"), nullptr);
}

}  // namespace
