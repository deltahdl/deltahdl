#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

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
