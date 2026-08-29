#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"

using namespace delta;

// Whether a run reported the one error a case is about, and it fails when no
// error the run recorded answers all three of: a message containing `message`,
// a location on line `line` of the source, and `subclause` named as the rule of
// IEEE 1800-2023 the report enforces. The failure lists every diagnostic the
// run did record, so a case that fired on some other cause says which one.
//
// A case that hands deltahdl an illegal source and asserts only
// DiagEngine::HasErrors() is satisfied by any rejection. It therefore passes
// when a different rule was broken, and passes when the source never reached
// the construct the case was written for:
// SinglePassPrecompile.DescriptionClaimedByTwoLibrariesNamesBothInItsDiagnostic
// in test/src/unit/test_parser_subclause_33_05_01.cpp handed the compiler
// `module cell;` until commit 28234b4ac, and Table B.1 reserves `cell`, so the
// source never parsed and the case covered nothing while passing. Naming the
// three answers that. The message and the subclause say which rule was
// enforced, and the line says where the source broke it, which is what tells
// two breaches of one rule apart.
//
// The three arguments are one call rather than three expectations because a
// case that names two of them and forgets the third still reads as complete.
//
// `message` is matched as a substring rather than compared whole, because a
// report assembled while the design runs carries a name or a value the literal
// at the emission site does not hold: src/preprocessor/preprocessor_lines.cpp
// builds its sentence from the directive it read and " illegal inside a design
// element". Pass a part of the sentence no other report produces. Nothing here
// checks that, and a substring several reports share proves as little as the
// count it replaced.
//
// The engine records a location and a subclause on a warning as well, and this
// answers for errors alone, because a source a case expects rejected is
// rejected by an error. ReportedWarning below answers the same three questions
// of a warning, for a case whose rule is enforced by one: §23.3.2.1 has the
// binder warn about an ordered port connection past the last port rather than
// reject the source, and a case reading that report through this one would
// fail whatever the run recorded.
// The 1-based line of `where` that `what` first stands on, or 0 when `where`
// writes it nowhere. The line argument below is a number a case can read off
// its own source only when the case wrote the input out; an input a tool
// produced puts the construct on a line nobody chose, and this is how such a
// case still names the line rather than dropping it.
inline uint32_t LineHolding(std::string_view where, std::string_view what) {
  size_t at = where.find(what);
  if (at == std::string_view::npos) return 0;
  uint32_t line = 1;
  for (size_t i = 0; i < at; ++i) {
    if (where[i] == '\n') ++line;
  }
  return line;
}

// `severity` is the only thing that separates the two callers below, so the
// word naming it in the failure message is derived here rather than passed
// beside it: taking both would give this six parameters, and
// readability-function-size.ParameterThreshold in
// etc/clang_tidy/test_src_unit.yml allows five.
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

inline ::testing::AssertionResult ReportedWarning(
    const std::vector<Diagnostic>& diags, std::string_view message,
    uint32_t line, std::string_view subclause) {
  return ReportedAt(diags, DiagSeverity::kWarning, message, line, subclause);
}
