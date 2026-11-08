#include "elaborator/sequence_admits_empty.h"

#include <string>
#include <string_view>

namespace delta {

SemanticLeadingClock InheritedLeadingClock() {
  SemanticLeadingClock c;
  c.inherited = true;
  c.event_expression.clear();
  return c;
}

SemanticLeadingClock ExplicitLeadingClock(std::string_view event_expression) {
  SemanticLeadingClock c;
  c.inherited = false;
  c.event_expression.assign(event_expression);
  return c;
}

std::string KappaForLocalVarRewrite(const SemanticLeadingClock& leading_clock) {
  if (leading_clock.inherited) return std::string{};
  return "@(" + leading_clock.event_expression + ")";
}

bool AdmitsEmpty(AdmitsEmptyForm form, bool first_child_admits_empty,
                 bool second_child_admits_empty) {
  switch (form) {
    case AdmitsEmptyForm::kBoolean:
      return false;
    case AdmitsEmptyForm::kLocalVarDeclThenRest:
      return first_child_admits_empty;
    case AdmitsEmptyForm::kOneTickWithLocalVarAssignment:
      return false;
    case AdmitsEmptyForm::kParenthesized:
      return first_child_admits_empty;
    case AdmitsEmptyForm::kDelay1:
      return first_child_admits_empty && second_child_admits_empty;
    case AdmitsEmptyForm::kDelay0:
      return false;
    case AdmitsEmptyForm::kOr:
      return first_child_admits_empty || second_child_admits_empty;
    case AdmitsEmptyForm::kIntersect:
      return first_child_admits_empty && second_child_admits_empty;
    case AdmitsEmptyForm::kFirstMatch:
      return first_child_admits_empty;
    case AdmitsEmptyForm::kStarZero:
      return true;
    case AdmitsEmptyForm::kPlusBounded:
    case AdmitsEmptyForm::kClockedAt:
      return first_child_admits_empty;
  }
  return false;
}

SequenceLocalVarDeclRewrite RewriteSequenceLocalVarDecl(
    bool rest_admits_empty) {
  if (rest_admits_empty) return SequenceLocalVarDeclRewrite::kSimplifiedEmpty;
  return SequenceLocalVarDeclRewrite::kSimplifiedNonEmpty;
}

PushRouting RoutePush(PushSite site, bool list_empty, bool right_admits_empty) {
  switch (site) {
    case PushSite::kLocalVarDeclThenProp:
      return PushRouting::kPrependLocalVarDecl;
    case PushSite::kLocalVarAssignThenProp:
      return PushRouting::kPrependLocalVarAssignment;
    case PushSite::kSequenceAsProperty:
    case PushSite::kOverlappingImplication:
      if (list_empty) return PushRouting::kRecurseInner;
      return PushRouting::kAttachKappaWithDelayZero;
    case PushSite::kNonoverlappingImplication:
      if (list_empty) return PushRouting::kRecurseInner;
      if (right_admits_empty) return PushRouting::kRecurseBothBranches;
      return PushRouting::kAttachKappaWithDelayZero;
    case PushSite::kIfElse:
      if (list_empty) return PushRouting::kRecurseBothBranches;
      return PushRouting::kGuardWithImplicationThenBranches;
    case PushSite::kDisableIff:
    case PushSite::kClockedAtProp:
    case PushSite::kParenthesized:
    case PushSite::kNot:
      return PushRouting::kRecurseInner;
    case PushSite::kOr:
    case PushSite::kAnd:
      return PushRouting::kRecurseBothBranches;
  }
  return PushRouting::kRecurseInner;
}

}  // namespace delta
