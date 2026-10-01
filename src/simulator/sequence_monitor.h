#pragma once

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "simulator/instance_bindings.h"
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

// §16.9.3: the sampled value functions `e` holds, appended to `sites`, so
// that the history each looks back through is sampled at every tick of the
// clock it is read on whether or not an attempt reads it there.
void CollectPastDirectedSites(const Expr* e, std::vector<const Expr*>& sites);

// §16.13.6 with §23.6: the end point of the sequence a hierarchical name
// `u.s` selects, the event `u.__seq_s` the monitor of the sequence s fires in
// the instance u; empty where the name has no dot or selects no instance's
// sequence.
std::string HierarchicalEndPoint(std::string_view path, SimContext& ctx);

// §16.12.2: one attempt of a sequence begun at one tick, kept apart from the
// others as first_match keeps them, for a property that reads the sequence
// as one operand. StepSequenceAttempt advances it one tick, `begin` where
// the tick is the one it begins at, and says whether it matched at the
// tick, can no longer match, or is still in flight.
struct LinearSequenceAttempt;

// kMatched says the attempt matched at the tick and may match again, and
// kMatchedLast that it matched with no attempt of the sequence left in
// flight.
enum class SequenceStep : uint8_t { kPending, kMatched, kMatchedLast, kFailed };

LinearSequenceAttempt* NewSequenceAttempt(const LinearSequence& body,
                                          Arena& arena);

SequenceStep StepSequenceAttempt(const LinearSequence& body,
                                 LinearSequenceAttempt& attempt, bool begin,
                                 SimContext& ctx, Arena& arena);

// §16.12.2: the attempts in flight of one sequential property, over its
// sequence flattened as a named sequence's is. CreateSequencePropertyState
// answers nullptr where the sequence is not one the monitor reads.
struct SequencePropertyState;

SequencePropertyState* CreateSequencePropertyState(const ModuleItem* seq,
                                                   SimContext& ctx,
                                                   Arena& arena);

enum class SequenceVerdict : uint8_t { kMatched, kFailed };

// What one tick of the property asks: `disabled` says the disable
// condition is true at this tick, which drops every attempt in flight and
// begins none; §16.14.3: `every_match` keeps an attempt that matched in
// flight while it can match again, so that each later match of it is a
// verdict too, as a cover sequence counts every match of an attempt, where
// a property holds at the first; `instances` are the attempts beginning at
// the tick, one entry, null, for a static assertion and, §16.14.6, the
// values each matured instance of a procedural one saved (§16.14.6.1).
struct SequenceTick {
  bool disabled = false;
  bool every_match = false;
  std::vector<const InstanceBindings*> instances;
};

// The verdict one attempt reached at a tick, with the values its instance
// saved for the action block to read, null for a static assertion's.
struct SequenceOutcome {
  SequenceVerdict verdict = SequenceVerdict::kFailed;
  const InstanceBindings* bindings = nullptr;
};

// One tick of the property: every attempt in flight advances and the new
// ones begin, each that matches at this tick or can no longer match
// reaching its verdict and leaving. The sampled value functions the
// sequence holds are sampled at the tick first.
std::vector<SequenceOutcome> AdvanceSequenceProperty(
    SequencePropertyState& state, const SequenceTick& tick, SimContext& ctx,
    Arena& arena);

// The attempts still in flight, which a strong property has fail when the
// run ends.
size_t PendingSequenceAttempts(const SequencePropertyState& state);

// §20.11: Kill aborts every attempt in flight, which reaches no verdict.
void AbortSequencePropertyAttempts(SequencePropertyState& state);

}  // namespace delta
