#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// §12.7.6: the forever-loop repeatedly executes a statement and states no
// condition under which it stops, so it describes a process rather than logic.
// The report names the loop and stands at the `forever`, which is what tells
// it apart from the other nine constructs the same walk rejects.
TEST(ForeverLoopSynthesis, ForeverIsRejectedByName) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  reg x;\n"
                           "  always begin\n"
                           "    forever x = 1;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  const Diagnostic* d = FindDiag(f, "forever loop is not synthesizable");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->subclause, "12.7.6");
  EXPECT_EQ(d->loc.line, 4u);
}

}  // namespace
