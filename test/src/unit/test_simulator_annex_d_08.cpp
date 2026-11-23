#include <gtest/gtest.h>

#include "helpers_annex_d_call_forms.h"

namespace {

constexpr const char* kResetForm =
    "$reset is written as a task statement with no argument list or with a "
    "stop value, then optionally a reset value and a diagnostics value, and "
    "this call is not";

constexpr const char* kResetCountForm =
    "$reset_count is written with no argument, and this call is not";

constexpr const char* kResetValueForm =
    "$reset_value is written with no argument, and this call is not";

TEST(ResetTaskForm, DISABLED_AnEmptyArgumentListIsReported) {
  ExpectOnlyTheMalformedCallReported("$reset", "$reset()", kResetForm, "D.8");
}

TEST(ResetTaskForm, DISABLED_AFourthArgumentIsReported) {
  ExpectOnlyTheMalformedCallReported("$reset(1, 42, 3)", "$reset(1, 42, 3, 4)",
                                     kResetForm, "D.8");
}

TEST(ResetTaskForm, DISABLED_AnEmptyStopValueIsReported) {
  ExpectOnlyTheMalformedCallReported("$reset(1, 42)", "$reset(, 42)",
                                     kResetForm, "D.8");
}

TEST(ResetTaskForm, DISABLED_ResetUsedAsAFunctionIsReported) {
  ExpectOnlyTheMalformedCallReported("$reset", "v = $reset", kResetForm, "D.8");
}

TEST(ResetTaskForm, DISABLED_AnArgumentToResetCountOrResetValueIsReported) {
  ExpectOnlyTheMalformedCallReported("v = $reset_count", "v = $reset_count(1)",
                                     kResetCountForm, "D.8");
  ExpectOnlyTheMalformedCallReported("v = $reset_value", "v = $reset_value(1)",
                                     kResetValueForm, "D.8");
}

}  // namespace
