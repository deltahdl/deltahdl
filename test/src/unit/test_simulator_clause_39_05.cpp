// §39.5: Control functions

#include "simulation/dpi_runtime.h"
#include "vpi/sv_vpi_user.h"
#include <cstdint>
#include <gtest/gtest.h>
#include <string>
#include <vector>

using namespace delta;

namespace {

TEST(Api, AssertionSeverityLevels) {
  AssertionApi api;
  api.SetSeverity("assert_a", AssertionSeverity::kWarning);
  api.SetSeverity("assert_b", AssertionSeverity::kFatal);

  EXPECT_EQ(api.GetSeverity("assert_a"), AssertionSeverity::kWarning);
  EXPECT_EQ(api.GetSeverity("assert_b"), AssertionSeverity::kFatal);
  // Default for unknown assertion.
  EXPECT_EQ(api.GetSeverity("unknown"), AssertionSeverity::kError);
}

TEST(Api, AssertionActionTypes) {
  AssertionApi api;
  api.SetAction("assert_x", AssertionAction::kDisable);
  EXPECT_EQ(api.GetAction("assert_x"), AssertionAction::kDisable);

  api.SetAction("assert_x", AssertionAction::kReset);
  EXPECT_EQ(api.GetAction("assert_x"), AssertionAction::kReset);

  // Default for unknown.
  EXPECT_EQ(api.GetAction("unknown"), AssertionAction::kNone);
}

TEST(SvVpiUser, AssertionCallbackReasons) {
  EXPECT_EQ(cbAssertionStart, 606);
  EXPECT_EQ(cbAssertionSuccess, 607);
  EXPECT_EQ(cbAssertionFailure, 608);
  EXPECT_EQ(cbAssertionDisable, 611);
  EXPECT_EQ(cbAssertionKill, 614);
}

TEST(SvVpiUser, AssertionControlConstants) {
  EXPECT_EQ(vpiAssertionDisable, 620);
  EXPECT_EQ(vpiAssertionEnable, 621);
  EXPECT_EQ(vpiAssertionReset, 622);
  EXPECT_EQ(vpiAssertionKill, 623);
}

TEST(SvVpiUser, RegisterAssertionCbReturnsNull) {
  vpiHandle result =
      vpi_register_assertion_cb(nullptr, cbAssertionStart, nullptr, nullptr);
  EXPECT_EQ(result, nullptr);
}

} // namespace
