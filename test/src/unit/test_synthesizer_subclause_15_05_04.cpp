#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// §15.5.4: `wait_order` suspends the calling process until the named events are
// triggered in the given order, and fails when one of them arrives out of turn.
// Suspending a process is not something a net does, and the order the construct
// polices is a property of a simulation run rather than of a circuit. The
// report names `wait_order` rather than the plain wait statement of §9.4.3,
// because the two block on different things and only one of them appears here.
TEST(EventSequencingSynthesis, WaitOrderIsRejectedByName) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  event a, b, c;\n"
                           "  reg x;\n"
                           "  always begin\n"
                           "    wait_order(a, b, c);\n"
                           "    x = 1;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  const Diagnostic* d =
      FindDiag(f, "wait_order construct is not synthesizable");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->subclause, "15.5.4");
  EXPECT_EQ(d->loc.line, 5u);
}

}  // namespace
