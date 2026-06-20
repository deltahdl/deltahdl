#pragma once

#include <cstdint>
#include <string>
#include <string_view>

namespace delta {

// §F.4.3 names the leading clock either "inherited" or some explicit clocking
// event @(c). We expose both states through a small tagged value.
struct SemanticLeadingClock {
  bool inherited = true;
  std::string event_expression;
};

SemanticLeadingClock InheritedLeadingClock();
SemanticLeadingClock ExplicitLeadingClock(std::string_view event_expression);

// §F.4.3 defines the kappa (κ) helper: when the sequence's leading clock is
// inherited, κ(r) is the empty string; otherwise it is "@(c)" where c is the
// leading clock event.
std::string KappaForLocalVarRewrite(const SemanticLeadingClock& leading_clock);

// §F.4.3 enumerates the sequence forms used as arguments to admits_empty. The
// rewriting algorithm requires knowing which form a sub-expression takes,
// because the answer depends entirely on that form.
enum class AdmitsEmptyForm : uint8_t {
  kBoolean,
  kLocalVarDeclThenRest,
  kOneTickWithLocalVarAssignment,
  kParenthesized,
  kDelay1,
  kDelay0,
  kOr,
  kIntersect,
  kFirstMatch,
  kStarZero,
  kPlusBounded,
  kClockedAt,
};

// §F.4.3 gives a piecewise rule for admits_empty. Each entry below names one
// rewrite case (boolean, sequence concatenation, repetition, etc.). The
// callers pass the relevant sub-answers; the function applies the rule and
// returns the answer for the composite form. Callers do not need to model the
// full AST: each form's rule reduces to a Boolean predicate over the
// children's admits_empty answers.
bool AdmitsEmpty(AdmitsEmptyForm form, bool first_child_admits_empty,
                 bool second_child_admits_empty);

// §F.4.3 closes by defining `push(E, p)` (and the analogous push for
// sequences); each line of the definition routes the local variable
// declaration list E into the right syntactic slot of the surrounding
// property/sequence. We model the push site rather than the full AST.
enum class PushSite : uint8_t {
  kLocalVarDeclThenProp,
  kLocalVarAssignThenProp,
  kSequenceAsProperty,
  kOverlappingImplication,
  kNonoverlappingImplication,
  kIfElse,
  kDisableIff,
  kClockedAtProp,
  kParenthesized,
  kNot,
  kOr,
  kAnd,
};

// §F.4.3 makes the push for a sequence-as-property branch depend on whether
// the sequence admits an empty match: an empty-admitting nonoverlapping
// implication antecedent uses a different push rule. We model the routing
// decision so callers can pick the right branch.
enum class PushRouting : uint8_t {
  kPrependLocalVarDecl,
  kPrependLocalVarAssignment,
  kAttachKappaWithDelayZero,
  kAttachKappaToBothSides,
  kRecurseBothBranches,
  kRecurseInner,
  kAttachKappaWithDelayOneToBoth,
};

PushRouting RoutePush(PushSite site, bool list_empty, bool right_admits_empty);

}  // namespace delta
