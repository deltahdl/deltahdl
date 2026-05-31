#pragma once

#include <cstdint>

#include "common/types.h"

namespace delta {

// §17.7.3 describes the scheduling semantics of the statements and constructs
// that live inside a checker. These helpers encode that region placement as
// pure functions, mapping each kind of checker statement onto the simulation
// region in which it is scheduled, so each rule can be observed in isolation.

// §17.7.3: classification of a checker's statements by how they are scheduled.
enum class CheckerStatementKind : uint8_t {
  // Constructs sensitive to changes, such as clocking events and continuous
  // assignments.
  kChangeSensitive,
  // Blocking statements appearing in the checker body.
  kBlocking,
  // A nonblocking assignment to a checker variable.
  kCheckerVariableNonblocking,
};

// §17.7.3: change-sensitive constructs and all blocking statements of a checker
// are scheduled in the Reactive region (as for programs); the nonblocking
// assignments of checker variables instead schedule their updates in the Re-NBA
// region. Returns the home region for the given kind of checker statement.
Region HomeRegionForCheckerStatement(CheckerStatementKind kind);

// §17.7.3: concurrent assertions have invariant scheduling semantics whether
// they appear in checker code or in design code. Given the region in which a
// concurrent assertion is scheduled in design code, returns the region used in
// checker code; the two are always identical.
Region ConcurrentAssertionRegionInChecker(Region region_in_design_code);

}  // namespace delta
