#include "elaborator/checker_procedures.h"

namespace delta {

bool ProceduralBlockAllowedInChecker(ProceduralBlockKind kind) {
  switch (kind) {
    case ProceduralBlockKind::kInitial:
    case ProceduralBlockKind::kFinal:
    case ProceduralBlockKind::kAlwaysComb:
    case ProceduralBlockKind::kAlwaysLatch:
    case ProceduralBlockKind::kAlwaysFf:
      // §17.5 lists initial, always, and final procedures as allowed, and
      // narrows the always procedures to always_comb, always_latch, and
      // always_ff.
      return true;
    case ProceduralBlockKind::kAlways:
      // §17.5 does not include the general-purpose always among the permitted
      // always forms.
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
      // §17.5 admits let declarations, the three assertion kinds, and a timing
      // control built from an event control.
      return true;
    case CheckerInitialContent::kDelayTimingControl:
    case CheckerInitialContent::kWaitTimingControl:
      // §17.5 restricts the procedure's timing control to an event control
      // only, so delay- and wait-based forms are excluded.
      return false;
  }
  return false;
}

bool CheckerAlwaysStatementAllowed(CheckerAlwaysStatement stmt,
                                   CheckerAlwaysForm form) {
  switch (stmt) {
    case CheckerAlwaysStatement::kBlockingAssignment:
      // §17.5: blocking assignments are allowed in always_comb and always_latch
      // procedures only.
      return form == CheckerAlwaysForm::kAlwaysComb ||
             form == CheckerAlwaysForm::kAlwaysLatch;
    case CheckerAlwaysStatement::kTimingEventControl:
      // §17.5: timing event control is allowed in always_ff procedures only.
      return form == CheckerAlwaysForm::kAlwaysFf;
    case CheckerAlwaysStatement::kNonblockingAssignment:
    case CheckerAlwaysStatement::kSelectionStatement:
    case CheckerAlwaysStatement::kLoopStatement:
    case CheckerAlwaysStatement::kSubroutineCall:
    case CheckerAlwaysStatement::kImmediateAssertion:
    case CheckerAlwaysStatement::kDeferredAssertion:
    case CheckerAlwaysStatement::kConcurrentAssertion:
    case CheckerAlwaysStatement::kLetDeclaration:
      // §17.5 lists these statements without tying them to a particular always
      // form, so each is allowed in all three.
      return true;
  }
  return false;
}

bool CheckerAlwaysExpressionIsSampled(
    CheckerAlwaysForm form, CheckerAlwaysExpressionPosition position) {
  switch (form) {
    case CheckerAlwaysForm::kAlwaysFf:
      // §17.5: in an always_ff procedure every expression except those used in
      // the event control is sampled.
      return position == CheckerAlwaysExpressionPosition::kBody;
    case CheckerAlwaysForm::kAlwaysComb:
    case CheckerAlwaysForm::kAlwaysLatch:
      // §17.5: expressions in always_comb and always_latch procedures are not
      // implicitly sampled.
      return false;
  }
  return false;
}

bool CheckerProcedureClockInferenceFollowsSection16146() {
  // §17.5 defers clock inference for checker procedures to §16.14.6.
  return true;
}

bool CheckerFinalProcedureIsAllowed() {
  // §17.5: a final procedure may be specified within a checker as in a module.
  return true;
}

bool CheckerFinalProcedureRunsOncePerInstantiation() {
  // §17.5: a checker final procedure executes once at the end of simulation for
  // every instantiation of the checker.
  return true;
}

bool CheckerFinalProceduresHaveImpliedOrdering() {
  // §17.5: there is no implied ordering among multiple final procedures.
  return false;
}

bool CheckerFinalProcedureDependsOnInstantiationContext() {
  // §17.5: the operation of a checker final procedure is independent of the
  // checker's instantiation context.
  return false;
}

bool CheckerFinalProcedureAllowsConstruct(bool allowed_in_non_checker_final) {
  // §17.5: a checker final procedure may include any construct allowed in a
  // non-checker final procedure — exactly that set, no wider and no narrower.
  return allowed_in_non_checker_final;
}

}  // namespace delta
