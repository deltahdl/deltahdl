#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

constexpr std::string_view kDollarParam =
    "holds '$', so it may stand only where '$' itself may";

inline void ExpectDollarParamReportedOnlyOn(
    const ElabFixture& f, std::initializer_list<uint32_t> reported,
    std::initializer_list<uint32_t> accepted) {
  for (uint32_t line : reported) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kDollarParam, line, "6.20.7"))
        << line;
  }
  for (uint32_t line : accepted) {
    EXPECT_FALSE(
        ReportedError(f.diag.Diagnostics(), kDollarParam, line, "6.20.7"))
        << line;
  }
}
