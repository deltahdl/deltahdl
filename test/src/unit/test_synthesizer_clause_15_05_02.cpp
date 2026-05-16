#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// §15.5.2: "The basic mechanism to wait for an event to be triggered
// is via the event control operator, @. The @ operator blocks the
// calling process until the given event is triggered." Process
// suspension on a named event is a simulation-only synchronization;
// it has no hardware equivalent and shall not be synthesizable when
// it appears in an always block.
TEST(NamedEventWaitSynthesis, RejectAtEventWaitInAlways) {
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
  EXPECT_TRUE(f.diag.HasErrors());
}

// §15.5.2: The bare-form wait syntax "@ hierarchical_event_identifier;"
// is the same blocking mechanism as @(ev) and is likewise not
// synthesizable when placed in an always block.
TEST(NamedEventWaitSynthesis, RejectBareAtEventWaitInAlways) {
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
  EXPECT_TRUE(f.diag.HasErrors());
}

// §15.5.2: An @-wait followed by a null statement still suspends the
// calling process and likewise has no hardware equivalent.
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
  EXPECT_TRUE(f.diag.HasErrors());
}

// §15.5.2 ↔ §15.5 cross-reference: §15.5 specifies the trigger operator
// "->" that the §15.5.2 wait pairs with. The trigger itself manipulates
// a simulation-time synchronization object and is not synthesizable
// either; rejecting it inside a synthesizable block guards the same
// wait/trigger pair the wait test above guards.
TEST(NamedEventWaitSynthesis, RejectEventTriggerInAlways) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  event ev;\n"
                           "  reg x;\n"
                           "  always begin -> ev; x = 1; end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
