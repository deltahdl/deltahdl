#include "simulator/checker_scheduling_semantics.h"

#include "simulator/scheduler.h"

namespace delta {

Region HomeRegionForCheckerStatement(CheckerStatementKind kind) {
  switch (kind) {
    case CheckerStatementKind::kChangeSensitive:
    case CheckerStatementKind::kBlocking:
      // §17.7.3: change-sensitive constructs and blocking statements are
      // scheduled "similarly to programs" (§24.3.1). Reuse the very same
      // scheduler placement the program-reactive path applies to a blocking
      // assignment rather than restating the region, so the two stay in lock
      // step: both land in the Reactive region.
      return Scheduler::HomeRegionForReactiveBlockingAssign();
    case CheckerStatementKind::kCheckerVariableNonblocking:
      // §17.7.3: a nonblocking assignment of a checker variable schedules its
      // update in the Re-NBA region. That region is exactly the reactive-set
      // dual of the ordinary NBA region, which is how the program path routes a
      // nonblocking assignment made in a reactive context — so derive it from
      // the shared mapping instead of naming Re-NBA directly.
      return Scheduler::ReactiveSetDualOf(Region::kNBA);
  }
  return Scheduler::HomeRegionForReactiveBlockingAssign();
}

Region ConcurrentAssertionRegionInChecker(Region region_in_design_code) {
  // §17.7.3: concurrent assertions keep the same scheduling semantics whether
  // present in checker code or design code, so the region is unchanged.
  return region_in_design_code;
}

}  // namespace delta
