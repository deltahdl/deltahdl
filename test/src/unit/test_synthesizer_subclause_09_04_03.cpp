#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// A wait statement written on the same line as the `always` it sits under is
// still reported at the `wait`, since the report stands at the statement
// rather than at the procedure holding it.
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

// A wait statement inside an initial procedure draws no §9.4.3 report at all.
// SynthLower::CheckSynthesizable passes over the body of an initial or a final
// procedure and reports the procedure itself under §9.2.1 when the module
// describes no other hardware, so the `wait` below is never examined. The case
// says which of the two reports the module gets, because asserting only that
// something was reported reads as coverage of §9.4.3 that this source cannot
// give.
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

// Syntax 9-5 gives the wait statement a statement_or_null body, and a wait
// written with the null one is rejected on its own account: the report comes
// from the `wait` rather than from walking a body, which a source with no body
// to walk is what shows.
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

// §9.4.3: a wait statement blocks until a condition becomes true, which no
// hardware does, and it is a different construct from the delay control of
// §9.4.1. The report names it and stands at the `wait`.
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
  const Diagnostic* d = FindDiag(f, "wait statement is not synthesizable");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->subclause, "9.4.3");
  EXPECT_EQ(d->loc.line, 5u);
}

}  // namespace
