#pragma once

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "lexer/token.h"
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

// §16.10 and §6.8: the width of a local declared with a data type keyword,
// 1 for a bit type.
uint32_t LocalWidth(TokenKind type_kw);
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
// a property holds at the first; `begin` is the number of attempts
// beginning at the tick, one for a static assertion and, §16.14.6, one per
// matured instance of a procedural one.
struct SequenceTick {
  bool disabled = false;
  bool every_match = false;
  uint32_t begin = 1;
};

// One tick of the property: every attempt in flight advances and the new
// ones begin, each that matches at this tick or can no longer match
// reaching its verdict and leaving. The sampled value functions the
// sequence holds are sampled at the tick first.
std::vector<SequenceVerdict> AdvanceSequenceProperty(
    SequencePropertyState& state, const SequenceTick& tick, SimContext& ctx,
    Arena& arena);

// The attempts still in flight, which a strong property has fail when the
// run ends.
size_t PendingSequenceAttempts(const SequencePropertyState& state);

}  // namespace delta
