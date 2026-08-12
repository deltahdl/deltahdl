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
// rejected by an error.
inline ::testing::AssertionResult ReportedError(
    const std::vector<Diagnostic>& diags, std::string_view message,
    uint32_t line, std::string_view subclause) {
  for (const auto& diag : diags) {
    if (diag.severity == DiagSeverity::kError &&
        diag.message.find(message) != std::string::npos &&
        diag.loc.line == line && diag.subclause == subclause) {
      return ::testing::AssertionSuccess();
    }
  }
  ::testing::AssertionResult failure = ::testing::AssertionFailure();
  failure << "no error containing \"" << message << "\" stands at line " << line
          << " under §" << subclause << "; the run reported";
  if (diags.empty()) failure << " nothing";
  for (const auto& diag : diags) {
    failure << "\n  "
            << (diag.severity == DiagSeverity::kError ? "error"
                                                      : "not an error")
            << " at line " << diag.loc.line << " under §"
            << (diag.subclause.empty() ? "(none)" : diag.subclause) << ": "
            << diag.message;
  }
  return failure;
}
