#include "elaborator/checker_rewrite_algorithm.h"

#include <optional>

#include "elaborator/rewrite_algorithm.h"

namespace delta {

CheckerRewriteStage FirstCheckerRewriteStage() {
  return CheckerRewriteStage::kCheckerInstances;
}

CheckerRewriteStage NextCheckerRewriteStage(CheckerRewriteStage) {
  return CheckerRewriteStage::kCheckerInstances;
}

std::optional<ActualArgumentSource> CheckerActualArgumentFor(
    bool bound_in_instance, bool default_declared) {
  return ActualArgumentFor(bound_in_instance, default_declared);
}

bool CheckerAlgorithmHandlesFormal(FormalKind kind) {
  switch (kind) {
    case FormalKind::kUntyped:
    case FormalKind::kTypedNonMatching:
    case FormalKind::kTypedMatching:
      return true;
    case FormalKind::kLocalVariable:
      return false;
  }
  return false;
}

ReferenceReplacement ReplaceCheckerFormalReference(FormalKind kind,
                                                   ActualNature actual) {
  return ReplaceFormalReference(kind, actual);
}

CastReplacedFormalLvalueRule CheckerCastReplacedFormalLvalueRule() {
  CastReplacedFormalLvalueRule rule;
  rule.replacement_may_be_lvalue = false;
  rule.scope = LvalueProhibitionScope::kWholeChecker;
  return rule;
}

bool CheckerParenthesizedActualNeedsParentheses(
    bool reference_already_parenthesized) {
  return ParenthesizedActualNeedsParentheses(reference_already_parenthesized);
}

FlattenedCheckerShape FlattenedCheckerForm() {
  FlattenedCheckerShape shape;
  shape.prepends_local_var_declarations = false;
  shape.appends_match_item_assignments = false;
  shape.enclosed_in_parentheses = false;
  return shape;
}

}  // namespace delta
