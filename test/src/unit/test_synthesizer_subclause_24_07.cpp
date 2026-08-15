#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

namespace {

// §24.7 rules that calling $exit "from a thread or its descendant thread that
// does not originate in an initial procedure in a program shall be ignored",
// and the always_ff procedure below is such a thread. Ignored at simulation is
// not synthesizable, so the synthesizer still withholds the netlist, and it
// reports the call as the §5.6.3 system task it is rather than under §24.7:
// the subclause governs what a program does with $exit, not what hardware the
// call describes.
TEST(ProgramControlTasksSynth, ExitOutsideAProgramInitialIsStillReported) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic clk;\n"
                           "  logic q;\n"
                           "  always_ff @(posedge clk) begin\n"
                           "    q <= 1'b0;\n"
                           "    $exit();\n"
                           "  end\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "system task or system function '$exit' is not synthesizable", 6,
      "5.6.3"));
}

}  // namespace
