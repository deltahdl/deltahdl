#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// A disable fork standing after a statement the synthesizer does lower is
// still reported, and at its own line rather than at the block's.
TEST(DisableForkSynthesis, RejectDisableForkInAlwaysComb) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input clk,\n"
                           "         output logic q);\n"
                           "  always_comb begin\n"
                           "    q = 0;\n"
                           "    disable fork;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "disable fork statement is not synthesizable", 5,
                            "9.6.3"));
}

// The report stands wherever the disable fork stands, so a sequential
// procedure gets it as a combinational one does.
TEST(DisableForkSynthesis, RejectDisableForkInAlwaysFF) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input clk,\n"
                           "         output logic q);\n"
                           "  always_ff @(posedge clk) begin\n"
                           "    disable fork;\n"
                           "    q <= 1;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "disable fork statement is not synthesizable", 4,
                            "9.6.3"));
}

// §9.6.3: a disable fork statement terminates every descendant subprocess of
// the calling process, which is a different construct from the disable
// statement of §9.6.2. The report names it and stands at the `disable`.
TEST(DisableForkSynthesis, DisableForkIsRejectedByName) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(output logic q);\n"
                           "  always_comb begin\n"
                           "    q = 0;\n"
                           "    disable fork;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  const Diagnostic* d =
      FindDiag(f, "disable fork statement is not synthesizable");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->subclause, "9.6.3");
  EXPECT_EQ(d->loc.line, 4u);
}

}  // namespace
