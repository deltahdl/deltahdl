#pragma once

#include <cstdint>
#include <set>
#include <string>
#include <string_view>

#include "elaborator/sequence_admits_empty.h"

namespace delta {

std::string_view InheritedSentinel();

bool IsInheritedSentinel(std::string_view s);

using LeadingClockSet = std::set<std::string>;

SemanticLeadingClock SequenceLeadingClockOfBareSequence();
SemanticLeadingClock SequenceLeadingClockAfterAtC(
    std::string_view c, const SemanticLeadingClock& inner);
SemanticLeadingClock SequenceLeadingClockOfParenthesized(
    const SemanticLeadingClock& inner);
SemanticLeadingClock SequenceLeadingClockOfDelay(
    const SemanticLeadingClock& left, const SemanticLeadingClock&);

enum class PropertyLeadingClockForm : uint8_t {
  kStrongOfMulticlockedSeq,
  kWeakOfMulticlockedSeq,
  kBareProperty,
  kClockedAtProperty,
  kParenthesized,
  kNot,
  kAnd,
  kOr,
  kOverlappingImplication,
  kNonoverlappingImplication,
  kIfThen,
  kIfElse,
  kCase,
  kNexttime,
  kAlways,
  kSEventually,
  kUntil,
  kUntilWith,
  kAcceptOn,
  kRejectOn,
  kSyncAcceptOn,
  kSyncRejectOn,
};

LeadingClockSet LeadingClockSetOf(PropertyLeadingClockForm form,
                                  const LeadingClockSet& a_set,
                                  const LeadingClockSet& b_set,
                                  std::string_view enclosing_clock,
                                  const SemanticLeadingClock& seq_unique);

LeadingClockSet LeadingClockSetOfPropertyInstance(
    const LeadingClockSet& flattened_body_set);

bool HasUniqueSemanticLeadingClock(const LeadingClockSet& s);

}  // namespace delta
