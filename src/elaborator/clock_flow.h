#ifndef DELTA_ELABORATOR_CLOCK_FLOW_H
#define DELTA_ELABORATOR_CLOCK_FLOW_H

#include <cstdint>
#include <string>
#include <vector>

namespace delta {

// Models clock flow, the propagation of a clocking-event scope through a
// multiclocked sequence or property, per IEEE 1800-2023 §16.13.3.
//
// A clocking-event scope is represented by the identifier of the clocking event
// currently in scope; the empty string denotes that no clocking event is in
// scope yet.
using ClockScope = std::string;

// §16.13.3: an operator's flow behavior with respect to a clocking-event scope.
enum class ClockFlowOperator : std::uint8_t {
  // Linear operators carry the scope from one operand to the next, left to
  // right (repetition, concatenation, negation, implication, followed-by, and
  // the nexttime, always, and eventually operators). A clocking event written
  // at one operand replaces the flowing scope for the operands that follow it.
  kLinear,
  // Branching operators distribute the incoming scope independently to each
  // operand (conjunction, disjunction, intersection, if-else, and the until
  // operators). A clocking event written in one operand does not reach a
  // sibling operand.
  kBranching,
};

// One operand of an operator, tagged with the clocking event explicitly written
// at its head. The empty string means the operand specifies no clock of its own
// and is therefore governed by whatever scope flows into it.
struct ClockFlowOperand {
  ClockScope explicit_clock;
};

// §16.13.3: resolve the clocking event governing each operand of an operator of
// the given kind, given the scope `incoming` at the operator and the operands
// in source order. The flowing scope is replaced by a clocking event written at
// an operand; for a linear operator the replacement persists to the operands
// that follow, while for a branching operator each operand starts from
// `incoming`.
std::vector<ClockScope> ResolveOperandClocks(
    ClockFlowOperator kind, const ClockScope& incoming,
    const std::vector<ClockFlowOperand>& operands);

// §16.13.3: the scope that flows into a parenthesized subexpression. The
// surrounding scope flows in unchanged (and, for a sequence, governs the inside
// left to right unless replaced there).
ClockScope ClockEnteringParentheses(const ClockScope& incoming);

// §16.13.3: the scope in effect immediately after a parenthesized
// subexpression. A clocking event introduced inside (here `interior_terminal`)
// does not flow out of the enclosing parentheses, so the surrounding scope is
// unchanged from `incoming`.
ClockScope ClockAfterParentheses(const ClockScope& incoming,
                                 const ClockScope& interior_terminal);

// §16.13.3: a method applied to an instance of a named property or sequence.
// The clocking-event scope flows into the instance regardless of which (if any)
// of these is applied.
enum class InstanceMethod : std::uint8_t {
  kNone,
  kTriggered,
  kMatched,
};

// §16.13.3: the scope that flows into an instance of a named property or
// sequence. The surrounding scope flows in unchanged, regardless of whether the
// `triggered` or `matched` method is applied to the instance.
ClockScope ClockEnteringInstance(const ClockScope& incoming,
                                 InstanceMethod method);

// §16.13.3: the scope in effect immediately after an instance of a named
// property or sequence. A clocking event in the declaration (here
// `declaration_clock`) does not flow out of the instance, so the surrounding
// scope is unchanged from `incoming`.
ClockScope ClockAfterInstance(const ClockScope& incoming,
                              const ClockScope& declaration_clock);

// §16.13.3: the scope that flows into the disable condition of `disable iff`.
// The surrounding scope does not flow in, so the disable condition carries no
// clocking event in scope regardless of `incoming`.
ClockScope ClockEnteringDisableCondition(const ClockScope& incoming);

// §16.13.3: juxtaposing two clocking events nullifies the first; `@(d) @(c) x`
// is equivalent to `@(c) x`. Given the clock written first (`first`) and the
// clock written immediately after it (`second`), the effective scope is
// `second`, which immediately overrides `first`.
ClockScope JuxtaposedClockingEvent(const ClockScope& first,
                                   const ClockScope& second);

}  // namespace delta

#endif  // DELTA_ELABORATOR_CLOCK_FLOW_H
