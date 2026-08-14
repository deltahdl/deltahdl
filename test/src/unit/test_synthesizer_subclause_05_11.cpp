#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// The test fails on a run that answers a netlist for a module whose assignment
// to an element of an unpacked array the synthesizer never lowers. §11.5.2
// defines array addressing, `mem_name[addr_expr]`, and this synthesizer builds
// nothing for it in either direction, so `assign arr[0] = 8'hAA;` has no
// lowering and `SynthLower::Lower` answers null.
//
// Until this change the case asserted only that `SynthLower::Lower` answered a
// graph. That held while both assignments were dropped from the graph in
// silence, so what it was asserting over was a netlist that never drives
// `arr`. The case names the report as well as the null answer, so it states
// which rule fired rather than passing on any refusal the run happens to make.
TEST(ArrayLiteralSynthesis, AssignToAnArrayElementIsReportedRatherThanDropped) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] arr [0:1];\n"
                           "  assign arr[0] = 8'hAA;\n"
                           "  assign arr[1] = 8'hBB;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment target has no lowering", 3, ""));
}

}  // namespace
