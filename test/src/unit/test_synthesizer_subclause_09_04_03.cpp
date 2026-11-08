#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(LevelSensitiveEventSynthesis, RejectWaitInAlways) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic ready;\n"
                           "  reg x;\n"
                           "  always begin wait(ready) x = 1; end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "wait statement is not synthesizable", 4, "9.4.3"));
}

TEST(LevelSensitiveEventSynthesis,
     WaitInsideInitialProcedureDrawsTheProcedureReport) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic ready;\n"
                           "  reg x;\n"
                           "  initial wait(ready) x = 1;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "initial procedure is not synthesizable", 4,
                            "9.2.1"));
  EXPECT_EQ(FindDiag(f, "wait statement is not synthesizable"), nullptr);
}

TEST(LevelSensitiveEventSynthesis, WaitWithNullBodyIsReportedAtTheWait) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic ready;\n"
                           "  always\n"
                           "    wait(ready) ;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "wait statement is not synthesizable", 4, "9.4.3"));
}

TEST(LevelSensitiveEventSynthesis, WaitStatementIsRejectedByName) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic ready;\n"
                           "  reg x;\n"
                           "  always begin\n"
                           "    wait(ready) x = 1;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "wait statement is not synthesizable", 5, "9.4.3"));
}

}  // namespace
