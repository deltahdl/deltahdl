#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §31.3.5: a basic `$recovery` command should elaborate without errors when
// the reference and data terminals resolve in scope.
TEST(SystemTimingCheckElaboration, RecoveryElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $recovery(posedge rst, posedge clk, 5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.3.5 Table 31-5: the notifier argument is optional. The four-argument
// form with a notifier variable must elaborate.
TEST(SystemTimingCheckElaboration, RecoveryWithNotifierElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $recovery(posedge rst, posedge clk, 5, ntfr);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.3.5 Table 31-5: the limit is a constant expression, so a specparam
// reference must resolve and elaborate.
TEST(SystemTimingCheckElaboration, RecoverySpecparamLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tRec = 7;\n"
      "    $recovery(posedge rst, posedge clk, tRec);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
