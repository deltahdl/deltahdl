#pragma once

#include <cstddef>
#include <string>
#include <vector>

#include "parser/ast.h"
#include "simulator/sequence_flatten.h"

namespace delta {

struct SimCoroutine;
class SimContext;
class Arena;

// §16.13.6/§9.4.4: a coroutine that watches `clock` and fires the endpoint
// event named `ep_name` at every tick the sequence whose flattened linear form
// is `body` reaches an end point at, so procedural `sequence.triggered` and
// `wait(seq.triggered)` observe the match. Created only for sequences whose
// linear body the parser captured and FlattenLinearSequence resolved.
SimCoroutine MakeSequenceMonitorCoroutine(LinearSequence body,
                                          std::vector<EventExpr> clock,
                                          std::string ep_name, SimContext& ctx,
                                          Arena& arena);

// §16.12.2: the attempts in flight of one sequential property, over its
// sequence flattened as a named sequence's is. CreateSequencePropertyState
// answers nullptr where the sequence is not one the monitor reads.
struct SequencePropertyState;

SequencePropertyState* CreateSequencePropertyState(const ModuleItem* seq,
                                                   SimContext& ctx,
                                                   Arena& arena);

enum class SequenceVerdict { kMatched, kFailed };

// One tick of the property: every attempt in flight advances and a new one
// begins, each that matches at this tick or can no longer match reaching
// its verdict and leaving; `disabled` says the disable condition is true at
// this tick, which drops every attempt in flight and begins none. The
// sampled value functions the sequence holds are sampled at the tick first.
std::vector<SequenceVerdict> AdvanceSequenceProperty(
    SequencePropertyState& state, bool disabled, SimContext& ctx, Arena& arena);

// The attempts still in flight, which a strong property has fail when the
// run ends.
size_t PendingSequenceAttempts(const SequencePropertyState& state);

}  // namespace delta
