#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §31.3.4: a basic `$removal` command should elaborate without errors when
// the reference and data terminals resolve in scope.
TEST(SystemTimingCheckElaboration, RemovalElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $removal(posedge rst, posedge clk, 5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.3.4 Table 31-4: the notifier argument is optional. The four-argument
// form with a notifier variable must elaborate.
TEST(SystemTimingCheckElaboration, RemovalWithNotifierElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $removal(posedge rst, posedge clk, 5, ntfr);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.3.4 Table 31-4: the limit is a constant expression, so a specparam
// reference must resolve and elaborate.
TEST(SystemTimingCheckElaboration, RemovalSpecparamLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tRem = 3;\n"
      "    $removal(posedge rst, posedge clk, tRem);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
