#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "simulation/dpi_runtime.h"

using namespace delta;

// =============================================================================
// S39: Assertion API
// =============================================================================

TEST(Api, AssertionRegisterCallback) {
  AssertionApi api;
  bool fired = false;
  api.RegisterCallback(
      kCbAssertionFailure,
      [&fired](const AssertionCbData& /*d*/) { fired = true; }, nullptr);
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
      [&fire_count](const AssertionCbData& /*d*/) { ++fire_count; }, nullptr);

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

TEST(Api, AssertionMultipleCallbacks) {
  AssertionApi api;
  int count_a = 0;
  int count_b = 0;
  api.RegisterCallback(
      kCbAssertionStart,
      [&count_a](const AssertionCbData& /*d*/) { ++count_a; }, nullptr);
  api.RegisterCallback(
      kCbAssertionStart,
      [&count_b](const AssertionCbData& /*d*/) { ++count_b; }, nullptr);
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

// =============================================================================
// S40: Coverage API
// =============================================================================

TEST(Api, CoverageControlStartStop) {
  CoverageApi cov;
  EXPECT_EQ(cov.GetControl(), CoverageControl::kStart);  // Default.

  cov.SetControl(CoverageControl::kStop);
  EXPECT_EQ(cov.GetControl(), CoverageControl::kStop);

  cov.SetControl(CoverageControl::kReset);
  EXPECT_EQ(cov.GetControl(), CoverageControl::kReset);
}

TEST(Api, CoverageGetMaxBins) {
  CoverageApi cov;
  EXPECT_EQ(cov.GetMaxBins(), 64u);  // Default.

  cov.SetMaxBins(128);
  EXPECT_EQ(cov.GetMaxBins(), 128u);
}

TEST(Api, CoverageActiveState) {
  CoverageApi cov;
  EXPECT_TRUE(cov.IsActive());  // Default.

  cov.SetActive(false);
  EXPECT_FALSE(cov.IsActive());
}

TEST(Api, CoverageDbAccess) {
  CoverageApi cov;
  cov.StoreValue("cg.cp.coverage", 75.0);
  EXPECT_DOUBLE_EQ(cov.GetValue("cg.cp.coverage"), 75.0);

  // Missing key returns 0.
  EXPECT_DOUBLE_EQ(cov.GetValue("nonexistent"), 0.0);
}

// =============================================================================
// S41: Data Read API
// =============================================================================

TEST(Api, DataReadGetPutValue) {
  DataReadApi api;
  DataReadValue val;
  val.format = DataReadFormat::kInt;
  val.int_val = 42;
  api.StoreVariable("x", val);

  auto result = api.GetValue("x", DataReadFormat::kInt);
  EXPECT_EQ(result.int_val, 42);
  EXPECT_EQ(result.format, DataReadFormat::kInt);
}

TEST(Api, DataReadPutValueOverwrites) {
  DataReadApi api;
  DataReadValue v1;
  v1.format = DataReadFormat::kInt;
  v1.int_val = 10;
  api.StoreVariable("sig", v1);

  DataReadValue v2;
  v2.format = DataReadFormat::kInt;
  v2.int_val = 99;
  api.PutValue("sig", v2);

  auto result = api.GetValue("sig", DataReadFormat::kInt);
  EXPECT_EQ(result.int_val, 99);
}

TEST(Api, DataReadRealFormat) {
  DataReadApi api;
  DataReadValue val;
  val.format = DataReadFormat::kReal;
  val.real_val = 3.14;
  api.StoreVariable("r", val);

  auto result = api.GetValue("r", DataReadFormat::kReal);
  EXPECT_DOUBLE_EQ(result.real_val, 3.14);
}

TEST(Api, DataReadStringFormat) {
  DataReadApi api;
  DataReadValue val;
  val.format = DataReadFormat::kString;
  val.str_val = "hello_sv";
  api.StoreVariable("s", val);

  auto result = api.GetValue("s", DataReadFormat::kString);
  EXPECT_EQ(result.str_val, "hello_sv");
}

TEST(Api, DataReadVectorFormat) {
  DataReadApi api;
  DataReadValue val;
  val.format = DataReadFormat::kVector;
  val.vector_val = {{0xDEADBEEF, 0}, {0xCAFEBABE, 0}};
  api.StoreVariable("vec", val);

  auto result = api.GetValue("vec", DataReadFormat::kVector);
  ASSERT_EQ(result.vector_val.size(), 2u);
  EXPECT_EQ(result.vector_val[0].aval, 0xDEADBEEFu);
  EXPECT_EQ(result.vector_val[1].aval, 0xCAFEBABEu);
}

TEST(Api, DataReadValueChangeCallback) {
  DataReadApi api;
  DataReadValue init;
  init.format = DataReadFormat::kInt;
  init.int_val = 0;
  api.StoreVariable("sig", init);

  bool cb_fired = false;
  int cb_new_val = 0;
  api.RegisterValueChangeCb("sig",
                            [&cb_fired, &cb_new_val](std::string_view /*name*/,
                                                     const DataReadValue& val) {
                              cb_fired = true;
                              cb_new_val = val.int_val;
                            });
  EXPECT_EQ(api.ValueChangeCbCount(), 1u);

  DataReadValue updated;
  updated.format = DataReadFormat::kInt;
  updated.int_val = 42;
  api.PutValue("sig", updated);

  EXPECT_TRUE(cb_fired);
  EXPECT_EQ(cb_new_val, 42);
}

TEST(Api, DataReadMissingVariableReturnsDefault) {
  DataReadApi api;
  auto result = api.GetValue("nonexistent", DataReadFormat::kInt);
  EXPECT_EQ(result.int_val, 0);
  EXPECT_EQ(result.format, DataReadFormat::kInt);
}
