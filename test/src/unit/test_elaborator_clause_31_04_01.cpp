#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §31.4.1 Syntax 31-9: the $skew command form with edge-qualified reference
// and data events plus a constant timing_check_limit must elaborate cleanly.
TEST(SystemTimingCheckElaboration, SkewElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $skew(posedge clk1, negedge clk2, 3);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.4.1 Syntax 31-9: the optional notifier slot must survive elaboration
// — it resolves to a variable identifier and must not trigger the extended
// argument paths reserved for sibling checks.
TEST(SystemTimingCheckElaboration, SkewWithNotifierElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $skew(posedge clk1, negedge clk2, 3, ntfr);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.4.1 Table 31-7: the limit is a non-negative *constant* expression, so
// an indirection through a specparam must flow through elaboration without
// error.
TEST(SystemTimingCheckElaboration, SkewSpecparamLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tSkew = 7;\n"
      "    $skew(posedge clk, d, tSkew);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.4.1 Table 31-7 / the zero-limit carve-out: the literal zero is a
// valid non-negative constant and must elaborate, since §31.4.1 explicitly
// defines $skew's behaviour when the skew limit value is zero.
TEST(SystemTimingCheckElaboration, SkewZeroLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $skew(posedge clk, d, 0);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
