#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(NetStrengths, ChargeStrengthAcceptedOnTrireg) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  trireg (large) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap") {
      EXPECT_EQ(net.charge_strength, Strength::kLarge);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(NetStrengths, ChargeStrengthRejectedOnNonTrireg) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module t;\n"
      "  wire (large) w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "charge strength can only be used with trireg nets",
                            2, "6.3.2.1"));
}

TEST(NetStrengths, DriveStrengthRejectedWithoutAssignment) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire (strong0, weak1) w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "drive strength on net declaration requires an assignment", 2, "6.3.2"));
}

TEST(NetStrengths, DriveStrengthAcceptedWithAssignment) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire (strong0, weak1) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
