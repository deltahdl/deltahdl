#pragma once

// §10.3.3 and §28.16: which of a continuous assignment's rise, fall and
// turn-off delays carries one transition of its target. Split out of
// simulator/lowerer_contassign.cpp, which lowers the assignment and runs the
// process that waits these delays out, because that file reached the line
// limit assert-no-oversized-source-files holds sources to; the choice of delay
// reads the two values and the delays and nothing of the process.

#include <cstdint>
#include <optional>

#include "common/types.h"

namespace delta {

class Arena;
class SimContext;
struct Expr;
struct RtlirContAssign;
struct RtlirNet;

// The delays an assignment's delay expressions evaluated to: `rise` always,
// `fall` and `decay` where the assignment wrote a second and a third.
struct ContAssignDelays {
  uint64_t rise = 0;
  uint64_t fall = 0;
  uint64_t decay = 0;
  bool has_fall = false;
  bool has_decay = false;
};

// §28.16: the delays a net declared with a net delay waits, its rise, fall and
// turn-off delays evaluated in the time unit `scale` of the module declaring
// it (§22.7); none for a net declared without one. Defined in
// simulator/contassign_delay.cpp.
std::optional<ContAssignDelays> NetDelayTicks(const RtlirNet& net,
                                              const TimeScale& scale,
                                              SimContext& ctx, Arena& arena);

// The delay §10.3.3 gives the transition of a `width`-bit target from
// `old_val` to `new_val`: Table 28-9 for a scalar, the clause's three rules
// for a vector. Defined in simulator/contassign_delay.cpp.
uint64_t SelectContAssignDelay(const Logic4Vec& old_val,
                               const Logic4Vec& new_val,
                               const ContAssignDelays& d, uint32_t width);

// §10.3.3 with §11.4.1: the target and the source of the assignment to a
// concatenation that one element's assignment was split from
// (EmitConcatContAssigns in src/elaborator/elaborator_cont_assign.cpp), both
// null for every other assignment.
struct ContAssignWhole {
  const Expr* lhs = nullptr;
  const Expr* rhs = nullptr;
};

// The whole assignment `ca` is an element of, read off the declaration it was
// built from. Defined in simulator/contassign_delay.cpp.
ContAssignWhole WholeOfConcatElement(const RtlirContAssign& ca);

// One transition of a target: the value it holds, the value arriving, and how
// many bits the two span.
struct ContAssignTransition {
  Logic4Vec old_val;
  Logic4Vec new_val;
  uint32_t width = 0;
};

// The delay `d` gives a transition of an assignment, `own` for an assignment
// of its own; for an element of `whole`, the whole assignment's -- its target
// as it stands and its source as it now evaluates -- so that every element
// settles after the one delay §10.3.3 picks for the assignment. Defined in
// simulator/contassign_delay.cpp.
uint64_t SelectTransitionDelay(const ContAssignWhole& whole,
                               const ContAssignTransition& own,
                               const ContAssignDelays& d, SimContext& ctx,
                               Arena& arena);

}  // namespace delta
