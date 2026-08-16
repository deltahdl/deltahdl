#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// §15.5.2's report reaches a named event whether the wait is written as the
// sensitivity list an `always` construct is built from or as an event control
// standing as a statement inside the block. SynthLower::CheckStmtSynthesizable
// asks NamedEventTerm about the terms of a StmtKind::kEventControl before
// NonSynthStmtRule, whose §9.4.2 entry covers every event control including
// the edge-sensitive ones this synthesizer does lower into flip-flops. The
// report stands at the event identifier.
TEST(NamedEventWaitSynthesis,
     NamedEventInEventControlStatementIsRejectedByName) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  event ev;\n"
                           "  reg x;\n"
                           "  always begin @(ev) x = 1; end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "named event in event control is not synthesizable",
                            4, "15.5.2"));
}

// The bare `@ev` form of the event control reaches the same report as the
// parenthesized `@(ev)` above, so neither spelling is the one that escapes
// §15.5.2's report while the other is caught.
TEST(NamedEventWaitSynthesis, BareNamedEventControlStatementIsRejectedByName) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  event ev;\n"
                           "  reg x;\n"
                           "  always begin @ev x = 1; end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "named event in event control is not synthesizable",
                            4, "15.5.2"));
}

// An `always` whose body is the null statement still has its sensitivity list
// read, so the named event in the list is reported even though there is no
// statement to lower. The report stands at the event identifier.
TEST(NamedEventWaitSynthesis, RejectAtEventWaitNullBody) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  event ev;\n"
                           "  always @(ev);\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "named event in event control is not synthesizable",
                            3, "15.5.2"));
}

// §15.5.2: the `@` operator blocks the calling process until the named event
// is triggered, so a sensitivity list built from one senses no net. The report
// names the construct and stands at the event identifier rather than at the
// `always`, which is what tells a design with several processes apart.
TEST(NamedEventWaitSynthesis, NamedEventInEventControlIsRejectedByName) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  event ev;\n"
                           "  reg x;\n"
                           "  always @(ev)\n"
                           "    x = 1;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "named event in event control is not synthesizable",
                            4, "15.5.2"));
}

}  // namespace
