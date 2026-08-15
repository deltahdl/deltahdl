#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// §16.17: the `expect` statement blocks the executing process until the given
// property succeeds or fails, and the statement after it is scheduled once the
// Observed region has finished evaluating that property. Both halves are
// simulation semantics: nothing in a netlist evaluates a property, and nothing
// in a netlist waits for a region. The report names the construct, because the
// action block hanging off an `expect` holds ordinary assignments that would
// otherwise be dropped along with it.
TEST(ExpectStatementSynthesis, ExpectIsRejectedByName) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input clk, input a, output reg q);\n"
                           "  always begin\n"
                           "    expect( @(posedge clk) a ) q = 1;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "expect statement is not synthesizable", 3,
                            "16.17"));
}

}  // namespace
