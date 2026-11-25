#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

namespace delta {

inline void ExpectTypeRefOperandReport(const std::string& source,
                                       std::string_view operand,
                                       uint32_t line) {
  SCOPED_TRACE(source);
  SimFixture f;
  ElaborateSrc(source, f);
  EXPECT_EQ(f.diag.Diagnostics().size(), operand == "pk::w9" ? 0U : 1U);
  if (operand == "nosuch") {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "parameter value assignment for type parameter "
                              "'T' of 'X' does not name a type",
                              line, "6.20.3"));
  } else if (operand.ends_with("u.hv")) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(),
                      "type operator argument uses a hierarchical reference, "
                      "which the type operator does not accept",
                      line, "6.23"));
  }
}

}  // namespace delta
