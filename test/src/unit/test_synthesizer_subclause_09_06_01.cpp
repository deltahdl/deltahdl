#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// §9.6.1: a wait fork statement blocks execution until every immediate child
// subprocess has terminated, which no hardware does. It is a different
// construct from the wait statement of §9.4.3 and from the disable fork
// statement of §9.6.3, and the report says which of the three it rejected.
TEST(WaitForkSynthesis, WaitForkIsRejectedByName) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  reg x;\n"
                           "  always begin\n"
                           "    x = 1;\n"
                           "    wait fork;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "wait fork statement is not synthesizable", 5,
                            "9.6.1"));
}

}  // namespace
