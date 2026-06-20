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
  // §F.4.3: when the unique semantic leading clock (defined in §16.16.1) is
  // inherited, the rewrite splices in nothing; otherwise it splices "@(c)".
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
      // §F.4.3: r[*0] always admits the empty match.
      return true;
    case AdmitsEmptyForm::kPlusBounded:
      // §F.4.3: r[*1:$] admits empty iff r does.
      return first_child_admits_empty;
    case AdmitsEmptyForm::kClockedAt:
      return first_child_admits_empty;
  }
  return false;
}

PushRouting RoutePush(PushSite site, bool list_empty, bool right_admits_empty) {
  switch (site) {
    case PushSite::kLocalVarDeclThenProp:
      return PushRouting::kPrependLocalVarDecl;
    case PushSite::kLocalVarAssignThenProp:
      return PushRouting::kPrependLocalVarAssignment;
    case PushSite::kSequenceAsProperty:
      // §F.4.3: if the local var list is empty, the rewrite collapses to the
      // sequence itself; otherwise it must splice in κ(r) ##0 r so the
      // assignments fire at the correct alignment.
      if (list_empty) return PushRouting::kRecurseInner;
      return PushRouting::kAttachKappaWithDelayZero;
    case PushSite::kOverlappingImplication:
      // §F.4.3: if the list is empty the implication's antecedent is left as
      // is; otherwise the rule splices κ(r) ##0 r |-> push(<>, p).
      if (list_empty) return PushRouting::kRecurseInner;
      return PushRouting::kAttachKappaWithDelayZero;
    case PushSite::kNonoverlappingImplication:
      // §F.4.3: nonoverlapping implication has a third branch — when the
      // antecedent admits an empty match the rewrite splits the case, so we
      // recurse into both branches rather than splicing once.
      if (list_empty) return PushRouting::kRecurseInner;
      if (right_admits_empty) return PushRouting::kRecurseBothBranches;
      return PushRouting::kAttachKappaWithDelayZero;
    case PushSite::kIfElse:
      return PushRouting::kRecurseBothBranches;
    case PushSite::kDisableIff:
      return PushRouting::kRecurseInner;
    case PushSite::kClockedAtProp:
      return PushRouting::kRecurseInner;
    case PushSite::kParenthesized:
      return PushRouting::kRecurseInner;
    case PushSite::kNot:
      return PushRouting::kRecurseInner;
    case PushSite::kOr:
    case PushSite::kAnd:
      return PushRouting::kRecurseBothBranches;
  }
  return PushRouting::kRecurseInner;
}

}  // namespace delta
