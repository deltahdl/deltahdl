#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// §15.5.1: the `->` operator makes an event occur, unblocking every process
// waiting on it, and no net carries that. Triggering an event is a different
// construct from waiting on one under §15.5.2, and the report says which of
// the two it rejected rather than reporting both in the same words.
TEST(EventTriggerSynthesis, EventTriggerIsRejectedByName) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  event ev;\n"
                           "  reg x;\n"
                           "  always begin\n"
                           "    -> ev;\n"
                           "    x = 1;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "event trigger is not synthesizable", 5, "15.5.1"));
}

// §15.5.1: the `->>` operator is the second of the two event triggers Syntax
// 15-1 defines, and it is not the first one under another spelling. It creates
// a nonblocking assign update event that triggers the event in a later region
// of the simulation cycle, so the statement after it runs before the event
// fires. The report names that construct rather than the blocking `->` above,
// since a reader told only "event trigger" would look for a `->` the source
// does not contain.
TEST(EventTriggerSynthesis, NonblockingEventTriggerIsRejectedByName) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  event ev;\n"
                           "  reg x;\n"
                           "  always begin\n"
                           "    ->> ev;\n"
                           "    x = 1;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "nonblocking event trigger is not synthesizable", 5,
                            "15.5.1"));
  EXPECT_EQ(FindDiag(f, "event trigger is not synthesizable"), nullptr);
}

}  // namespace
