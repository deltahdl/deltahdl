#pragma once

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

}  // namespace delta
