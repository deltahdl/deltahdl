#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"

constexpr uint32_t kOneTimeStepCheckLine = 5;

inline bool RanEdgesInOneTimeStep(std::string_view check, bool data_first,
                                  SimFixture& f) {
  std::string src =
      "module top(\n"
      "    output logic r,\n"
      "    output logic d);\n"
      "  specify\n"
      "    ";
  src += check;
  src +=
      "\n"
      "  endspecify\n"
      "  initial begin\n"
      "    r = 1'b0;\n"
      "    d = 1'b0;\n"
      "    #50 ";
  src +=
      data_first ? "d = 1'b1;\n    r = 1'b1;\n" : "r = 1'b1;\n    d = 1'b1;\n";
  src +=
      "  end\n"
      "endmodule\n";
  auto* rtl = ElaborateSrc(src, f);
  if (rtl == nullptr || f.has_errors) return false;
  LowerAndRun(rtl, f);
  return true;
}

inline ::testing::AssertionResult ViolatesInEitherOrder(
    std::string_view check, std::string_view message,
    std::string_view subclause) {
  for (bool data_first : {false, true}) {
    SimFixture f;
    if (!RanEdgesInOneTimeStep(check, data_first, f)) {
      return ::testing::AssertionFailure() << check << " did not run";
    }
    if (!ReportedWarning(f.diag.Diagnostics(), message, kOneTimeStepCheckLine,
                         subclause)) {
      return ::testing::AssertionFailure()
             << check << " reported no violation with the "
             << (data_first ? "data" : "reference") << " assigned first";
    }
  }
  return ::testing::AssertionSuccess();
}

inline ::testing::AssertionResult SilentInEitherOrder(
    std::string_view check, std::string_view message) {
  for (bool data_first : {false, true}) {
    SimFixture f;
    if (!RanEdgesInOneTimeStep(check, data_first, f)) {
      return ::testing::AssertionFailure() << check << " did not run";
    }
    if (FindDiag(f, message) != nullptr) {
      return ::testing::AssertionFailure()
             << check << " reported a violation with the "
             << (data_first ? "data" : "reference") << " assigned first";
    }
  }
  return ::testing::AssertionSuccess();
}
