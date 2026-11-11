#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"

using namespace delta;

inline uint32_t LineHolding(std::string_view where, std::string_view what) {
  size_t at = where.find(what);
  if (at == std::string_view::npos) return 0;
  uint32_t line = 1;
  for (size_t i = 0; i < at; ++i) {
    if (where[i] == '\n') ++line;
  }
  return line;
}

inline ::testing::AssertionResult ReportedAt(
    const std::vector<Diagnostic>& diags, DiagSeverity severity,
    std::string_view message, uint32_t line, std::string_view subclause) {
  for (const auto& diag : diags) {
    if (diag.severity == severity &&
        diag.message.find(message) != std::string::npos &&
        diag.loc.line == line && diag.subclause == subclause) {
      return ::testing::AssertionSuccess();
    }
  }
  const char* what = severity == DiagSeverity::kError ? "error" : "warning";
  ::testing::AssertionResult failure = ::testing::AssertionFailure();
  failure << "no " << what << " containing \"" << message
          << "\" stands at line " << line << " under §" << subclause
          << "; the run reported";
  if (diags.empty()) failure << " nothing";
  for (const auto& diag : diags) {
    failure << "\n  "
            << (diag.severity == DiagSeverity::kError ? "error" : "warning")
            << " at line " << diag.loc.line << " under §"
            << (diag.subclause.empty() ? "(none)" : diag.subclause) << ": "
            << diag.message;
  }
  return failure;
}

inline ::testing::AssertionResult ReportedError(
    const std::vector<Diagnostic>& diags, std::string_view message,
    uint32_t line, std::string_view subclause) {
  return ReportedAt(diags, DiagSeverity::kError, message, line, subclause);
}

inline bool ErrorOnLine(const std::vector<Diagnostic>& diags, uint32_t line) {
  for (const auto& diag : diags) {
    if (diag.severity == DiagSeverity::kError && diag.loc.line == line) {
      return true;
    }
  }
  return false;
}

inline ::testing::AssertionResult ReportedWarning(
    const std::vector<Diagnostic>& diags, std::string_view message,
    uint32_t line, std::string_view subclause) {
  return ReportedAt(diags, DiagSeverity::kWarning, message, line, subclause);
}
