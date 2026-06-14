#include "elaborator/checker_rewrite_algorithm.h"

namespace delta {

CheckerRewriteStage FirstCheckerRewriteStage() {
  return CheckerRewriteStage::kCheckerInstances;
}

CheckerRewriteStage NextCheckerRewriteStage(CheckerRewriteStage /*stage*/) {
  // The checker main loop drains a single kind of instance, so its only stage
  // is its own successor — there is no second pass to advance to.
  return CheckerRewriteStage::kCheckerInstances;
}

bool CheckerAlgorithmHandlesFormal(FormalKind kind) {
  switch (kind) {
    case FormalKind::kUntyped:          // step 3
    case FormalKind::kTypedNonMatching:  // step 4
    case FormalKind::kTypedMatching:     // step 5
      return true;
    case FormalKind::kLocalVariable:
      // A checker formal input argument is never a local variable; flatten_checker
      // has no step that prepends local variable declarations.
      return false;
  }
  return false;
}

ReferenceReplacement ReplaceCheckerFormalReference(FormalKind kind,
                                                   ActualNature actual) {
  // Steps 3–5 are the same per-reference substitution as §F.4.1.1; the checker
  // algorithm reuses that decision rather than re-deriving it.
  return ReplaceFormalReference(kind, actual);
}

Step4LvalueRule CheckerStep4LvalueRule() {
  // The step-4 replacement is a cast, which is never a variable_lvalue, and the
  // prohibition spans the whole checker.
  Step4LvalueRule rule;
  rule.replacement_may_be_lvalue = false;
  rule.scope = LvalueProhibitionScope::kWholeChecker;
  return rule;
}

}  // namespace delta
