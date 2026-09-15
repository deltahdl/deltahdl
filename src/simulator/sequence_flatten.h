#pragma once

#include <vector>

#include "parser/ast.h"

namespace delta {

class SimContext;
class Arena;

// The linear form of a named sequence after §16.8's instantiation has been
// applied to it: the Boolean operands matched along consecutive clock ticks,
// the §16.7 cycle delay before each, the first one the leading delay, and the
// clocking event the sequence is evaluated on, the sequence's own or the one an
// instance it contains supplies.
struct LinearSequence {
  std::vector<Expr*> operands;
  std::vector<SeqCycleDelay> delays;
  // §16.10: the match items each operand carries, parallel to the operands,
  // and the local variables of the flattened body, those the bodies declare
  // and, under names of their own, the local variable formal arguments of
  // the instances (§16.8.2).
  std::vector<std::vector<SeqMatchAssign>> match_items;
  // §16.9.2: the repetition each operand carries, parallel to the operands.
  std::vector<SeqRepetition> repetitions;
  std::vector<SeqLocalDecl> locals;
  std::vector<EventExpr> clock;
  // §16.9.6: the flattened forms of the other operands of the `intersect`
  // this chain is the first operand of, each matched from the same tick as
  // this one and ending at the same tick.
  std::vector<LinearSequence> intersects;
  // §16.9.5: the flattened forms of the other operands of the `and` this
  // chain is the first operand of, each, with its intersects, matched from
  // the same tick as this one, the whole ending at the later end point.
  std::vector<LinearSequence> conjuncts;
  // §16.9.7: the flattened forms of the body's other `or` operands, each
  // matched beside this one under the same clock.
  std::vector<LinearSequence> alternatives;
  // §16.9.8: whether the body is the operand of `first_match`, so that of
  // the matches of one attempt, over every `or` operand, only those ending
  // at the earliest tick count.
  bool first_match = false;
};

// §16.8: the sequential behaviour of an instance of a named sequence is that
// of the flattened sequence Annex F.4.1 obtains from the declaration's body by
// substituting the actual arguments for the references to the formals, and an
// instance stands anywhere a sequence_expr does, so an operand of `seq` that
// instantiates another named sequence is replaced by that sequence's own
// flattened operands with its formals' references replaced by the actuals
// bound by position or by name, a `$` actual bounding a delay range as the
// clause has it, and the delay before the instance and the instantiated body's
// leading delay adding. §16.8.1: an actual is cast to the type of a typed
// formal, and a formal of type event stands for the event expression passed
// to it, so a sequence declared without a clock takes the clock an instance in
// it names through such a formal, as one declared with a clock lends its own
// to the clockless sequences it instantiates. §16.8.2: a local variable formal
// argument is a local variable of the instance, a new copy of it made at each
// attempt, initialized from the actual before the instance's first operand is
// evaluated when its direction is input or inout, and assigned back to the
// actual's local variable when the instance matches when its direction is
// inout or output; every local of an instantiated body takes a name of its
// own in the flattened sequence. Answers false where `seq` has
// no linear body the parser captured, where an instance names a sequence that
// has none, or where instances nest past the depth a cyclic dependency, which
// §16.8 makes an error, would reach.
bool FlattenLinearSequence(const ModuleItem* seq, SimContext& ctx, Arena& arena,
                           LinearSequence& out);

}  // namespace delta
