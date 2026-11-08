#include "elaborator/semantic_leading_clock.h"

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
  if (inner.inherited) return ExplicitLeadingClock(c);
  return inner;
}

SemanticLeadingClock SequenceLeadingClockOfParenthesized(
    const SemanticLeadingClock& inner) {
  return inner;
}

SemanticLeadingClock SequenceLeadingClockOfDelay(
    const SemanticLeadingClock& left, const SemanticLeadingClock&) {
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
      if (seq_unique.inherited) return SingletonSet(InheritedSentinel());
      return SingletonSet(seq_unique.event_expression);
    case PropertyLeadingClockForm::kBareProperty:
      return SingletonSet(InheritedSentinel());
    case PropertyLeadingClockForm::kClockedAtProperty:
      return ReplaceInherited(a_set, enclosing_clock);
    case PropertyLeadingClockForm::kParenthesized:
    case PropertyLeadingClockForm::kNot:
      return a_set;
    case PropertyLeadingClockForm::kAnd:
    case PropertyLeadingClockForm::kOr:
      return UnionSets(a_set, b_set);
    case PropertyLeadingClockForm::kOverlappingImplication:
    case PropertyLeadingClockForm::kNonoverlappingImplication:
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
      return SingletonSet(InheritedSentinel());
    case PropertyLeadingClockForm::kAcceptOn:
    case PropertyLeadingClockForm::kRejectOn:
      return a_set;
  }
  return SingletonSet(InheritedSentinel());
}

LeadingClockSet LeadingClockSetOfPropertyInstance(
    const LeadingClockSet& flattened_body_set) {
  return flattened_body_set;
}

bool HasUniqueSemanticLeadingClock(const LeadingClockSet& s) {
  if (s.size() != 1) return false;
  return !IsInheritedSentinel(*s.begin());
}

}  // namespace delta
