#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
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
  const Diagnostic* d = FindDiag(f, "event trigger is not synthesizable");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->subclause, "15.5.1");
  EXPECT_EQ(d->loc.line, 5u);
}

}  // namespace
