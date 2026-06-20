#include "elaborator/semantic_leading_clock.h"

#include <algorithm>
#include <set>
#include <string>
#include <string_view>

#include "elaborator/sequence_admits_empty.h"

namespace delta {

namespace {
constexpr std::string_view kInheritedSentinel = "<inherited>";
}

std::string_view InheritedSentinel() { return kInheritedSentinel; }

bool IsInheritedSentinel(std::string_view s) { return s == kInheritedSentinel; }

SemanticLeadingClock SequenceLeadingClockOfBareSequence() {
  return InheritedLeadingClock();
}

SemanticLeadingClock SequenceLeadingClockAfterAtC(
    std::string_view c, const SemanticLeadingClock& inner) {
  // §16.16.1: when the inner leading clock is inherited, @(c) supplies c as
  // the new leading clock. Otherwise the inner clock is kept.
  if (inner.inherited) return ExplicitLeadingClock(c);
  return inner;
}

SemanticLeadingClock SequenceLeadingClockOfDelay(
    const SemanticLeadingClock& left, const SemanticLeadingClock& /*right*/) {
  // §16.16.1: m1 ##1 m2 and m1 ##0 m2 both keep m1's leading clock.
  return left;
}

static LeadingClockSet SingletonSet(std::string_view value) {
  LeadingClockSet s;
  s.emplace(value);
  return s;
}

static LeadingClockSet UnionSets(const LeadingClockSet& a,
                                 const LeadingClockSet& b) {
  LeadingClockSet r(a);
  r.insert(b.begin(), b.end());
  return r;
}

static LeadingClockSet ReplaceInherited(const LeadingClockSet& s,
                                        std::string_view replacement) {
  LeadingClockSet r;
  for (const auto& v : s) {
    if (IsInheritedSentinel(v)) {
      r.emplace(std::string{replacement});
    } else {
      r.insert(v);
    }
  }
  return r;
}

LeadingClockSet LeadingClockSetOf(PropertyLeadingClockForm form,
                                  const LeadingClockSet& a_set,
                                  const LeadingClockSet& b_set,
                                  std::string_view enclosing_clock,
                                  const SemanticLeadingClock& seq_unique) {
  switch (form) {
    case PropertyLeadingClockForm::kStrongOfMulticlockedSeq:
    case PropertyLeadingClockForm::kWeakOfMulticlockedSeq:
      // §16.16.1: strong(m) and weak(m) take their unique clock from m.
      if (seq_unique.inherited) return SingletonSet(InheritedSentinel());
      return SingletonSet(seq_unique.event_expression);
    case PropertyLeadingClockForm::kBareProperty:
      return SingletonSet(InheritedSentinel());
    case PropertyLeadingClockForm::kClockedAtProperty:
      // §16.16.1: @(c) q replaces inherited with c in q's clock set.
      return ReplaceInherited(a_set, enclosing_clock);
    case PropertyLeadingClockForm::kParenthesized:
    case PropertyLeadingClockForm::kNot:
      return a_set;
    case PropertyLeadingClockForm::kAnd:
    case PropertyLeadingClockForm::kOr:
      return UnionSets(a_set, b_set);
    case PropertyLeadingClockForm::kOverlappingImplication:
    case PropertyLeadingClockForm::kNonoverlappingImplication:
      // §16.16.1: m |-> p and m |=> p inherit m's set, not p's.
      return a_set;
    case PropertyLeadingClockForm::kIfThen:
    case PropertyLeadingClockForm::kIfElse:
    case PropertyLeadingClockForm::kCase:
    case PropertyLeadingClockForm::kNexttime:
    case PropertyLeadingClockForm::kAlways:
    case PropertyLeadingClockForm::kSEventually:
    case PropertyLeadingClockForm::kUntil:
    case PropertyLeadingClockForm::kUntilWith:
    case PropertyLeadingClockForm::kSyncAcceptOn:
    case PropertyLeadingClockForm::kSyncRejectOn:
      // §16.16.1: these forms always have the inherited singleton set.
      return SingletonSet(InheritedSentinel());
    case PropertyLeadingClockForm::kAcceptOn:
    case PropertyLeadingClockForm::kRejectOn:
      // §16.16.1: accept_on/reject_on keep the operand's clock set.
      return a_set;
  }
  return SingletonSet(InheritedSentinel());
}

LeadingClockSet LeadingClockSetOfPropertyInstance(
    const LeadingClockSet& flattened_body_set) {
  // §16.16.1: a property instance carries the same leading-clock set as the
  // flattened body it stands for.
  return flattened_body_set;
}

bool HasUniqueSemanticLeadingClock(const LeadingClockSet& s) {
  // §16.16.1 (referenced from §16.16's rule (e)): a maximal multiclocked
  // property must have a unique semantic leading clock. "Unique" means the
  // set has exactly one element and that element is not the inherited
  // sentinel — an inherited slot without an outer clock to fill it cannot
  // serve as the leading clock.
  if (s.size() != 1) return false;
  return !IsInheritedSentinel(*s.begin());
}

}  // namespace delta
