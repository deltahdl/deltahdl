// §31.9.1: Requirements for accurate simulation

#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;
using ConfigParseTest = ProgramTestParse;

namespace {

// =============================================================================
// §31.9 Extended $setuphold arguments
// =============================================================================
TEST_F(SpecifyTest, SetupholdWithDelayedSignals) {
  auto *cu =
      Parse("module m;\n"
            "specify\n"
            "  $setuphold(posedge clk, data, -10, 20, ntfr, , , dCLK, dD);\n"
            "endspecify\n"
            "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto &tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kSetuphold);
  EXPECT_EQ(tc.notifier, "ntfr");
  EXPECT_EQ(tc.delayed_ref, "dCLK");
  EXPECT_EQ(tc.delayed_data, "dD");
}

} // namespace
