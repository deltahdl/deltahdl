#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace delta {

struct MarkedSource {
  const char* where;
  std::string src;
  std::vector<std::string> reported;
  std::vector<std::string> accepted;
};

inline void ExpectMarkedReports(const MarkedSource& marked,
                                std::string_view message,
                                std::string_view subclause) {
  SCOPED_TRACE(marked.where);
  ElabFixture f;
  ElaborateSrc(marked.src, f);
  const auto& diags = f.diag.Diagnostics();
  for (const std::string& text : marked.reported) {
    uint32_t line = LineHolding(marked.src, text);
    EXPECT_NE(line, 0u) << text;
    EXPECT_TRUE(ReportedError(diags, message, line, subclause)) << text;
  }
  for (const std::string& text : marked.accepted) {
    uint32_t line = LineHolding(marked.src, text);
    EXPECT_NE(line, 0u) << text;
    EXPECT_FALSE(ErrorOnLine(diags, line)) << text;
  }
}

}  // namespace delta
