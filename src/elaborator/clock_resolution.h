#ifndef DELTA_ELABORATOR_CLOCK_RESOLUTION_H
#define DELTA_ELABORATOR_CLOCK_RESOLUTION_H

#include <cstdint>
#include <string>
#include <string_view>

#include "elaborator/semantic_leading_clock.h"

namespace delta {

// Models clock resolution, the determination of the leading clocking event of a
// concurrent assertion statement and the constraints clocking blocks impose on
// the sequences and properties inside them, per IEEE 1800-2023 §16.16.
//
// The "maximal property" referred to in the rules below is the unique flattened
// property of an assertion produced by the rewriting of §F.4.1 (a dependency of
// this subclause); the helpers here take its already-computed attributes as
// inputs rather than recomputing the flattening.

// §16.16: where a leading clocking event for a concurrent assertion comes from.
// The ordering of the rules establishes a precedence: an explicit event (rule
// d) beats a contextually inferred event (rule c), which beats the default
// clocking event (rule a); kNone means none of the three applies.
enum class LeadingClockOrigin : std::uint8_t {
  kNone,
  kExplicit,
  kInferred,
  kDefault,
};

// §16.16: the leading clocking event chosen for a concurrent assertion, paired
// with the rule that supplied it. `event` is empty exactly when `origin` is
// kNone.
struct AssertionLeadingClock {
  LeadingClockOrigin origin;
  std::string event;
};

// §16.16(a,c,d): resolve the leading clocking event of a concurrent assertion
// statement. An explicitly written leading clocking event takes precedence
// (rule d); failing that, a clocking event contextually inferred from an
// enclosing procedural block applies and supersedes the default (rule c);
// failing both, the default clocking event of the enclosing scope is used as
// though it had been written as the leading clocking event (rule a). An empty
// argument denotes the absence of that candidate.
AssertionLeadingClock ResolveConcurrentAssertionClock(
    std::string_view explicit_clock, std::string_view inferred_clock,
    std::string_view default_clock);

// §16.16(a): the default clocking event applies to a sequence or property
// *declaration* only when the declaration appears inside a clocking block whose
// clocking event is the default. Outside of that case a declaration never
// receives the default clock.
bool DefaultClockAppliesToDeclaration(bool declared_in_default_clocking_block);

// §16.16(b1): the prohibition on an explicit clocking event for a sequence or
// property declared inside a clocking block is enforced at the parser stage
// (parser_clocking.cpp), where the declaration's leading clock is visible on
// real source; see test_parser_clause_16_16.cpp.

// §16.16(b1): a sequence or property declared inside a clocking block is
// treated as though the block's clocking event had been written as its leading
// clocking event.
std::string ClockingBlockDeclarationLeadingClock(std::string_view block_clock);

// §16.16(b2): the prohibition on a multiclocked sequence or property inside a
// clocking block is enforced at the parser stage (parser_clocking.cpp), where
// the declaration's clocking events are counted on real source; see
// test_parser_clause_16_16.cpp.

// §16.16(b3): when a named sequence or property declared outside a clocking
// block is instantiated inside one, the instance must be singly clocked and its
// clocking event must be identical to that of the clocking block.
bool ClockingBlockExternalInstanceIsLegal(bool instance_is_multiclocked,
                                          std::string_view instance_clock,
                                          std::string_view block_clock);

// §16.16(e): a multiclocked maximal property of a concurrent assertion is legal
// only if it has a unique semantic leading clock as defined in §16.16.1.
bool MulticlockedMaximalPropertyIsLegal(const LeadingClockSet& clock_set);

// §16.16(f): a concurrent assertion with no explicit, inferred, or default
// leading clocking event is legal only when its maximal property is an instance
// of a sequence or property for which a unique leading clocking event is
// determined.
bool UnclockedAssertionIsLegal(bool maximal_property_is_instance,
                               bool instance_has_unique_leading_clock);

}  // namespace delta

#endif  // DELTA_ELABORATOR_CLOCK_RESOLUTION_H
