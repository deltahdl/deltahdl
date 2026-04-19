#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §31.3.6: a bare `$recrem` command should elaborate without errors when the
// reference and data terminals resolve in scope.
TEST(SystemTimingCheckElaboration, RecremElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $recrem(posedge clk, rst, 8, 3);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.3.6 Table 31-6: the notifier argument is optional. The five-argument
// form with a notifier variable must elaborate.
TEST(SystemTimingCheckElaboration, RecremWithNotifierElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $recrem(posedge clk, rst, 8, 3, ntfr);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Moved from A.7.5.1: the full Syntax 31-8 invocation — notifier plus the
// trailing pair of delayed signal identifiers — elaborates cleanly.
TEST(TimingCheckCommandElaboration, RecremFullArgsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $recrem(posedge clk, rst, 8, 3, ntfr, , , dCLK, dRST);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.3.6 Table 31-6: recovery_limit and removal_limit are constant
// expressions. Specparam-driven limits must resolve and elaborate.
TEST(SystemTimingCheckElaboration, RecremSpecparamLimitsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tRec = 8;\n"
      "    specparam tRem = 3;\n"
      "    $recrem(posedge clk, rst, tRec, tRem);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
