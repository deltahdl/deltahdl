#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
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
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(SynthLower, RejectDelayInInitial) {
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
  EXPECT_TRUE(f.diag.HasErrors());
}

// §9.4.1: a delay control is its own construct, so the report that rejects one
// names it and stands at the `#`. A report reading only that some statement is
// unsynthesizable, at no position at all, tells whoever wrote the design
// neither which rule was broken nor where.
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
  const Diagnostic* d = FindDiag(f, "delay control is not synthesizable");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->subclause, "9.4.1");
  EXPECT_EQ(d->loc.line, 4u);
}

// A module holding two rejectable constructs on different lines is reported at
// the one the walk reaches first, and the words name that one. Neither half is
// satisfied by a message change on its own: an empty location leaves both
// constructs at line 0, and one shared message leaves the wait statement and
// the delay control indistinguishable even once the location is filled in.
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
  const Diagnostic* d = FindDiag(f, "wait statement is not synthesizable");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->loc.line, 5u);
  EXPECT_EQ(FindDiag(f, "delay control is not synthesizable"), nullptr);
}

}  // namespace
