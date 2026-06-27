#pragma once

namespace delta {

struct ModuleItem;
struct SimCoroutine;
class SimContext;
class Arena;

// §16.13.6/§9.4.4: a coroutine that watches a named sequence's clock and fires
// its `__seq_<name>` endpoint event when the simple clocked linear body
// matches, so procedural `sequence.triggered` and `wait(seq.triggered)` observe
// the match. Created only for sequences whose linear body the parser captured.
SimCoroutine MakeSequenceMonitorCoroutine(const ModuleItem* seq,
                                          SimContext& ctx, Arena& arena);

}  // namespace delta
