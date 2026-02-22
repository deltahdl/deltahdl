// §39.5: Control functions

#include <gtest/gtest.h>
#include "vpi/sv_vpi_user.h"

namespace {

// =============================================================================
// Callback reason constants
// =============================================================================
TEST(SvVpiUser, AssertionCallbackReasons) {
  EXPECT_EQ(cbAssertionStart, 606);
  EXPECT_EQ(cbAssertionSuccess, 607);
  EXPECT_EQ(cbAssertionFailure, 608);
  EXPECT_EQ(cbAssertionDisable, 611);
  EXPECT_EQ(cbAssertionKill, 614);
}

// =============================================================================
// Assertion control constants
// =============================================================================
TEST(SvVpiUser, AssertionControlConstants) {
  EXPECT_EQ(vpiAssertionDisable, 620);
  EXPECT_EQ(vpiAssertionEnable, 621);
  EXPECT_EQ(vpiAssertionReset, 622);
  EXPECT_EQ(vpiAssertionKill, 623);
}

// =============================================================================
// Assertion callback registration function
// =============================================================================
TEST(SvVpiUser, RegisterAssertionCbReturnsNull) {
  vpiHandle result =
      vpi_register_assertion_cb(nullptr, cbAssertionStart, nullptr, nullptr);
  EXPECT_EQ(result, nullptr);
}

}  // namespace
