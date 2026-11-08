#include "simulator/checker_scheduling_semantics.h"

#include "common/types.h"
#include "simulator/scheduler.h"

namespace delta {

Region HomeRegionForCheckerStatement(CheckerStatementKind kind) {
  switch (kind) {
    case CheckerStatementKind::kChangeSensitive:
    case CheckerStatementKind::kBlocking:
      return Scheduler::HomeRegionForReactiveBlockingAssign();
    case CheckerStatementKind::kCheckerVariableNonblocking:
      return Scheduler::ReactiveSetDualOf(Region::kNBA);
  }
  return Scheduler::HomeRegionForReactiveBlockingAssign();
}

Region ConcurrentAssertionRegionInChecker(Region region_in_design_code) {
  return region_in_design_code;
}

}  // namespace delta
