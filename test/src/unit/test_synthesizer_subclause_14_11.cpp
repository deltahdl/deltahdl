#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// §14.11: `##` delays execution by a number of clocking block events, so the
// statement after it runs at a time the default clocking decides rather than at
// the time the source reaches it. No hardware holds a process back that way.
//
// The module below is legal: a default clocking block governs it, which is what
// §14.11 requires of a module using `##`, so the only thing wrong with it is
// that it is not hardware. The report has to say so by name, because a design
// carrying `##3` that lowered without a word would give a netlist in which `q`
// never takes the value the source assigns it.
TEST(CycleDelaySynthesis, CycleDelayIsRejectedByName) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input clk, input din, output reg q);\n"
                           "  logic sample;\n"
                           "  default clocking cb @(posedge clk);\n"
                           "    input sample;\n"
                           "  endclocking\n"
                           "  always begin\n"
                           "    ##3;\n"
                           "    q = din;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  const Diagnostic* d = FindDiag(f, "cycle delay is not synthesizable");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->subclause, "14.11");
  EXPECT_EQ(d->loc.line, 7u);
}

}  // namespace
