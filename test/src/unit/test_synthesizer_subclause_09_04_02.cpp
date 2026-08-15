#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(EventControlSynthesis, PosedgeEdgeIdentifierProducesLatches) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input clk, input [7:0] d,\n"
                           "         output logic [7:0] q);\n"
                           "  always_ff @(posedge clk) q <= d;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(aig->outputs.empty());
  EXPECT_FALSE(aig->latches.empty());
}

TEST(EventControlSynthesis, NegedgeEdgeIdentifierProducesLatches) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input clk, input [7:0] d,\n"
                           "         output logic [7:0] q);\n"
                           "  always_ff @(negedge clk) q <= d;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(aig->outputs.empty());
  EXPECT_FALSE(aig->latches.empty());
}

TEST(EventControlSynthesis, EdgeEdgeIdentifierProducesLatches) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input clk, input [7:0] d,\n"
                           "         output logic [7:0] q);\n"
                           "  always_ff @(edge clk) q <= d;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(aig->outputs.empty());
  EXPECT_FALSE(aig->latches.empty());
}

TEST(EventControlSynthesis, OrEdgeIdentifierListProducesLatches) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input clk, input rst_n,\n"
                           "         input [7:0] d, output logic [7:0] q);\n"
                           "  always_ff @(posedge clk or negedge rst_n)\n"
                           "    if (!rst_n) q <= 0;\n"
                           "    else q <= d;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(aig->outputs.empty());
  EXPECT_FALSE(aig->latches.empty());
}

TEST(EventControlSynthesis, NonEdgeEventExpressionIsCombinational) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input a, input b, output logic y);\n"
                           "  always @(a or b) y = a & b;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(aig->outputs.empty());
  EXPECT_TRUE(aig->latches.empty());
}

// §9.4.2: an event control reached as a statement, rather than as the leading
// timing control the sensitivity list is taken from, delays execution until a
// simulation event occurs. The report names it and stands at the `@`.
TEST(EventControlSynthesis, EventControlStmtIsRejectedByName) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  reg clk;\n"
                           "  reg x;\n"
                           "  always begin\n"
                           "    x = 1;\n"
                           "    @(posedge clk) x = 0;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "event control is not synthesizable", 6, "9.4.2"));
}

}  // namespace
