#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(LevelSensitiveSequenceSynthesis, InitialWithWaitTriggeredSkipped) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input clk, input [7:0] d,\n"
                           "         output logic [7:0] q);\n"
                           "  logic a, b, c;\n"
                           "  sequence abc;\n"
                           "    @(posedge clk) a ##1 b ##1 c;\n"
                           "  endsequence\n"
                           "  always_ff @(posedge clk)\n"
                           "    q <= d;\n"
                           "  initial begin\n"
                           "    wait(abc.triggered);\n"
                           "    $display(\"matched\");\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(aig->outputs.empty());
}

// §9.4.4 states its own construct as "the level-sensitive wait statement in
// conjunction with the built-in method that returns the current end status of
// a named sequence: triggered", so the statement the synthesizer meets is the
// §9.4.3 wait statement of Syntax 9-5 and the report names that subclause. A
// §9.4.4 report would be a second name for one construct, so the case asserts
// the §9.4.3 one rather than treating it as a report filed one subclause off.
TEST(LevelSensitiveSequenceSynthesis, RejectWaitTriggeredInAlways) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic clk, a, b;\n"
                           "  reg x;\n"
                           "  sequence ab;\n"
                           "    @(posedge clk) a ##1 b;\n"
                           "  endsequence\n"
                           "  always begin\n"
                           "    wait(ab.triggered) x = 1;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "wait statement is not synthesizable", 8, "9.4.3"));
}

}  // namespace
