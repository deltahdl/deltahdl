// §39.5: Control functions

#include <gtest/gtest.h>
#include <cstdint>
#include <string>
#include <vector>
#include "simulation/dpi_runtime.h"

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

}  // namespace
