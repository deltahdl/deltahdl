#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// §15.5.2's report reaches a named event named in the sensitivity list an
// `always` construct is built from, and not one named by an event control
// standing as a statement inside the block. SynthLower::CheckSynthesizable
// reads the list through NamedEventTrigger and reaches the statement through
// CheckStmtSynthesizable, which knows the kind and not what the kind waits on,
// so the source below draws the §9.4.2 report for an event control instead.
// The case names that report rather than claiming coverage of §15.5.2 it does
// not have.
TEST(NamedEventWaitSynthesis,
     NamedEventInEventControlStatementDrawsTheEventControlReport) {
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
                            "event control is not synthesizable", 4, "9.4.2"));
}

// The bare `@ev` form of the event control reaches the same report as the
// parenthesized `@(ev)` above, so neither spelling is the one that escapes
// §15.5.2's report while the other is caught.
TEST(NamedEventWaitSynthesis,
     BareNamedEventControlStatementDrawsTheEventControlReport) {
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
                            "event control is not synthesizable", 4, "9.4.2"));
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
  const Diagnostic* d =
      FindDiag(f, "named event in event control is not synthesizable");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->subclause, "15.5.2");
  EXPECT_EQ(d->loc.line, 4u);
}

}  // namespace
