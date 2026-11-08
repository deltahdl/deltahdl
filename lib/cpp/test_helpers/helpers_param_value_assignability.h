#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <format>
#include <span>
#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

struct IncompatibleValue {
  const char* where;
  const char* src;
  const char* param;
  uint32_t line;
};

inline std::string NotAssignable(std::string_view param) {
  return std::format(
      "the value given to parameter '{}' is not assignment compatible with "
      "its type",
      param);
}

inline void ExpectEachReported(std::span<const IncompatibleValue> cases) {
  for (const IncompatibleValue& value : cases) {
    SCOPED_TRACE(value.where);
    ElabFixture f;
    ElaborateSrc(value.src, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), NotAssignable(value.param),
                              value.line, "6.20.2"));
  }
}

inline void ExpectEachAccepted(std::span<const char* const> sources) {
  for (const char* src : sources) {
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_FALSE(f.has_errors);
  }
}
