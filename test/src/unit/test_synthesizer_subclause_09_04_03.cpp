#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
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
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(LevelSensitiveEventSynthesis, RejectWaitInInitial) {
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
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(LevelSensitiveEventSynthesis, RejectWaitNullBody) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic ready;\n"
                           "  initial wait(ready) ;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(f.diag.HasErrors());
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
