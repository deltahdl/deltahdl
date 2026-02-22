// §39.4: Dynamic information

#include "simulation/dpi_runtime.h"
#include "vpi/sv_vpi_user.h"
#include <cstdint>
#include <gtest/gtest.h>
#include <string>
#include <vector>

using namespace delta;

namespace {

// =============================================================================
// S39: Assertion API
// =============================================================================
TEST(Api, AssertionRegisterCallback) {
  AssertionApi api;
  bool fired = false;
  api.RegisterCallback(
      kCbAssertionFailure,
      [&fired](const AssertionCbData & /*d*/) { fired = true; }, nullptr);
  EXPECT_EQ(api.CallbackCount(), 1u);

  AssertionCbData data;
  data.reason = kCbAssertionFailure;
  api.FireCallback(data);
  EXPECT_TRUE(fired);
}

TEST(Api, AssertionCallbackReasonFiltering) {
  AssertionApi api;
  int fire_count = 0;
  api.RegisterCallback(
      kCbAssertionSuccess,
      [&fire_count](const AssertionCbData & /*d*/) { ++fire_count; }, nullptr);

  // Fire with non-matching reason.
  AssertionCbData data;
  data.reason = kCbAssertionFailure;
  api.FireCallback(data);
  EXPECT_EQ(fire_count, 0);

  // Fire with matching reason.
  data.reason = kCbAssertionSuccess;
  api.FireCallback(data);
  EXPECT_EQ(fire_count, 1);
}

TEST(Api, AssertionMultipleCallbacks) {
  AssertionApi api;
  int count_a = 0;
  int count_b = 0;
  api.RegisterCallback(
      kCbAssertionStart,
      [&count_a](const AssertionCbData & /*d*/) { ++count_a; }, nullptr);
  api.RegisterCallback(
      kCbAssertionStart,
      [&count_b](const AssertionCbData & /*d*/) { ++count_b; }, nullptr);
  EXPECT_EQ(api.CallbackCount(), 2u);

  AssertionCbData data;
  data.reason = kCbAssertionStart;
  api.FireCallback(data);
  EXPECT_EQ(count_a, 1);
  EXPECT_EQ(count_b, 1);
}

TEST(Api, AssertionCbDataFields) {
  AssertionCbData data;
  data.reason = kCbAssertionFailure;
  data.severity = AssertionSeverity::kFatal;
  data.action = AssertionAction::kKill;
  data.assertion_name = "my_assert";

  EXPECT_EQ(data.reason, kCbAssertionFailure);
  EXPECT_EQ(data.severity, AssertionSeverity::kFatal);
  EXPECT_EQ(data.action, AssertionAction::kKill);
  EXPECT_EQ(data.assertion_name, "my_assert");
}

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

} // namespace
