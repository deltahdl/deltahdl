#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §31.3.3: a bare `$setuphold` command should elaborate without errors when
// the reference and data terminals resolve in scope.
TEST(SystemTimingCheckElaboration, SetupholdElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setuphold(posedge clk, data, 10, 5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.3.3 Table 31-3: the notifier argument is optional. The five-argument
// form with a notifier variable must elaborate.
TEST(SystemTimingCheckElaboration, SetupholdWithNotifierElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setuphold(posedge clk, data, 10, 5, ntfr);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Moved from A.7.5.1: the full Syntax 31-5 invocation — notifier plus the
// trailing pair of delayed signal identifiers — elaborates cleanly.
TEST(TimingCheckCommandElaboration, SetupholdFullArgsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setuphold(posedge clk, data, 10, 5, ntfr, , , dCLK, dDATA);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.3.3 Table 31-3: setup_limit and hold_limit are constant expressions.
// Specparam-driven limits must resolve and elaborate.
TEST(SystemTimingCheckElaboration, SetupholdSpecparamLimitsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tSu = 10;\n"
      "    specparam tHo = 5;\n"
      "    $setuphold(posedge clk, data, tSu, tHo);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
