#pragma once

#include <cstdint>
#include <set>
#include <string>
#include <string_view>

#include "elaborator/sequence_admits_empty.h"

namespace delta {

// §16.16.1 distinguishes "inherited" leading clocks from explicit ones. The
// sentinel string captures the inherited case inside a set of clocks, where a
// dedicated reserved value is needed so the inherited element coexists with
// real clocks in the same container.
std::string_view InheritedSentinel();

bool IsInheritedSentinel(std::string_view s);

using LeadingClockSet = std::set<std::string>;

// §16.16.1 first defines the semantic leading clock of a multiclocked
// sequence as a unique value. The inductive rules are: a bare sequence is
// inherited; @(c) s replaces inherited with c (otherwise it inherits s's
// clock); a parenthesized (m) keeps m's clock; ##1 and ##0 keep the left
// operand's clock.
SemanticLeadingClock SequenceLeadingClockOfBareSequence();
SemanticLeadingClock SequenceLeadingClockAfterAtC(
    std::string_view c, const SemanticLeadingClock& inner);
SemanticLeadingClock SequenceLeadingClockOfParenthesized(
    const SemanticLeadingClock& inner);
SemanticLeadingClock SequenceLeadingClockOfDelay(
    const SemanticLeadingClock& left, const SemanticLeadingClock& /*right*/);

// §16.16.1 enumerates the property forms whose set of semantic leading
// clocks is given by a piecewise rule. Each entry below names one form; the
// callers supply the relevant sub-answers and we compute the resulting set.
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

// §16.16.1: compute the leading-clock set of a property form from its
// children's sets and the relevant clock event when the form is "@(c) q".
LeadingClockSet LeadingClockSetOf(PropertyLeadingClockForm form,
                                  const LeadingClockSet& a_set,
                                  const LeadingClockSet& b_set,
                                  std::string_view enclosing_clock,
                                  const SemanticLeadingClock& seq_unique);

// §16.16.1: the set of semantic leading clocks of a property instance equals
// the set computed for the multiclocked property obtained from the body of
// its declaration once actual arguments are substituted. The substitution is
// handled elsewhere; this returns the body's clock set unchanged.
LeadingClockSet LeadingClockSetOfPropertyInstance(
    const LeadingClockSet& flattened_body_set);

// §16.16.1 closes by saying the maximal multiclocked property of an assertion
// must have a unique semantic leading clock — i.e. the set must contain
// exactly one element, and that element must not be the inherited sentinel.
bool HasUniqueSemanticLeadingClock(const LeadingClockSet& s);

}  // namespace delta
