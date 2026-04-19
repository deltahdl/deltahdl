#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §31.3.2: a basic `$hold` command should elaborate without errors when
// the reference and data terminals resolve in scope.
TEST(SystemTimingCheckElaboration, HoldElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $hold(posedge clk, data, 5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.3.2 Table 31-2: the notifier argument is optional. The four-
// argument form with a notifier variable must elaborate.
TEST(SystemTimingCheckElaboration, HoldWithNotifierElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $hold(posedge clk, data, 5, ntfr);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
