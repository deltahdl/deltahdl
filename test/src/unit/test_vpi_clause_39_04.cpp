// §39.4: Dynamic information

#include <gtest/gtest.h>
#include "vpi/sv_vpi_user.h"

namespace {

// =============================================================================
// Assertion API structures
// =============================================================================
TEST(SvVpiUser, AssertionStepInfoStruct) {
  s_vpi_assertion_step_info info = {};
  info.matched_expression_count = 3;
  info.state_from = 1;
  info.state_to = 2;
  EXPECT_EQ(info.matched_expression_count, 3);
  EXPECT_EQ(info.state_from, 1);
  EXPECT_EQ(info.state_to, 2);
}

TEST(SvVpiUser, AttemptInfoStruct) {
  s_vpi_attempt_info info = {};
  info.attempt_start_time.type = vpiSimTime;
  info.attempt_start_time.low = 100;
  info.detail.fail_expr = nullptr;
  EXPECT_EQ(info.attempt_start_time.type, vpiSimTime);
  EXPECT_EQ(info.attempt_start_time.low, 100u);
}

}  // namespace
