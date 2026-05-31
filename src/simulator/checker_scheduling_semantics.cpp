#include "simulator/checker_scheduling_semantics.h"

namespace delta {

Region HomeRegionForCheckerStatement(CheckerStatementKind kind) {
  switch (kind) {
    case CheckerStatementKind::kChangeSensitive:
    case CheckerStatementKind::kBlocking:
      // §17.7.3: change-sensitive constructs and blocking statements land in
      // the Reactive region, just as they do for programs.
      return Region::kReactive;
    case CheckerStatementKind::kCheckerVariableNonblocking:
      // §17.7.3: nonblocking assignments of checker variables schedule their
      // updates in the Re-NBA region.
      return Region::kReNBA;
  }
  return Region::kReactive;
}

Region ConcurrentAssertionRegionInChecker(Region region_in_design_code) {
  // §17.7.3: concurrent assertions keep the same scheduling semantics whether
  // present in checker code or design code, so the region is unchanged.
  return region_in_design_code;
}

}  // namespace delta
