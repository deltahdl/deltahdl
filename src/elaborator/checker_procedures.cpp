#include "elaborator/checker_procedures.h"

namespace delta {

bool ProceduralBlockAllowedInChecker(ProceduralBlockKind kind) {
  switch (kind) {
    case ProceduralBlockKind::kInitial:
    case ProceduralBlockKind::kFinal:
    case ProceduralBlockKind::kAlwaysComb:
    case ProceduralBlockKind::kAlwaysLatch:
    case ProceduralBlockKind::kAlwaysFf:
      return true;
    case ProceduralBlockKind::kAlways:
      return false;
  }
  return false;
}

bool CheckerInitialProcedureAllows(CheckerInitialContent content) {
  switch (content) {
    case CheckerInitialContent::kLetDeclaration:
    case CheckerInitialContent::kImmediateAssertion:
    case CheckerInitialContent::kDeferredAssertion:
    case CheckerInitialContent::kConcurrentAssertion:
    case CheckerInitialContent::kEventTimingControl:
      return true;
    case CheckerInitialContent::kDelayTimingControl:
    case CheckerInitialContent::kWaitTimingControl:
      return false;
  }
  return false;
}

bool CheckerAlwaysStatementAllowed(CheckerAlwaysStatement stmt,
                                   CheckerAlwaysForm form) {
  switch (stmt) {
    case CheckerAlwaysStatement::kBlockingAssignment:
      return form == CheckerAlwaysForm::kAlwaysComb ||
             form == CheckerAlwaysForm::kAlwaysLatch;
    case CheckerAlwaysStatement::kTimingEventControl:
      return form == CheckerAlwaysForm::kAlwaysFf;
    case CheckerAlwaysStatement::kNonblockingAssignment:
    case CheckerAlwaysStatement::kSelectionStatement:
    case CheckerAlwaysStatement::kLoopStatement:
    case CheckerAlwaysStatement::kSubroutineCall:
    case CheckerAlwaysStatement::kImmediateAssertion:
    case CheckerAlwaysStatement::kDeferredAssertion:
    case CheckerAlwaysStatement::kConcurrentAssertion:
    case CheckerAlwaysStatement::kLetDeclaration:
      return true;
  }
  return false;
}

bool CheckerAlwaysExpressionIsSampled(
    CheckerAlwaysForm form, CheckerAlwaysExpressionPosition position) {
  switch (form) {
    case CheckerAlwaysForm::kAlwaysFf:
      return position == CheckerAlwaysExpressionPosition::kBody;
    case CheckerAlwaysForm::kAlwaysComb:
    case CheckerAlwaysForm::kAlwaysLatch:
      return false;
  }
  return false;
}

bool CheckerProcedureClockInferenceFollowsProceduralAssertionRules() {
  return true;
}

bool CheckerFinalProcedureIsAllowed() { return true; }

bool CheckerFinalProcedureRunsOncePerInstantiation() { return true; }

bool CheckerFinalProceduresHaveImpliedOrdering() { return false; }

bool CheckerFinalProcedureDependsOnInstantiationContext() { return false; }

bool CheckerFinalProcedureAllowsConstruct(bool allowed_in_non_checker_final) {
  return allowed_in_non_checker_final;
}

}  // namespace delta
