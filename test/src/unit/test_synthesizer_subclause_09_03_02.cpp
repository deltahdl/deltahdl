#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// §9.3.2: the fork-join parallel block creates a concurrent process from each
// of its statements, and a process is not a piece of combinational or
// sequential logic. The report calls the construct what the subclause calls it
// and stands at the `fork`, so a design holding several rejected constructs
// says which one failed and on which line.
TEST(ParallelBlockSynthesis, ForkJoinIsRejectedByName) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  reg x;\n"
                           "  always begin\n"
                           "    fork\n"
                           "      x = 1;\n"
                           "    join\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parallel block is not synthesizable", 4, "9.3.2"));
}

}  // namespace
