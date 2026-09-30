#pragma once

#include <cstddef>
#include <functional>
#include <vector>

#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"

namespace delta {

class SimContext;
class Arena;
struct Logic4Vec;

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
  // §16.13.1: the clocking event each operand is evaluated on where the
  // sequence names one before it, parallel to the operands once any does,
  // an operand under none evaluated on the leading clock; and, once the
  // property holding the sequence has numbered its clocks, the number of
  // each operand's clock, 0 the leading clock's.
  std::vector<std::vector<EventExpr>> operand_clocks;
  std::vector<int> operand_clock_index;
  // §16.13.3: the clock flowing out of the sequence's end, empty where the
  // one flowing in does, and its number once numbered.
  std::vector<EventExpr> clock_out;
  int clock_out_index = 0;
  // §16.13.3: the clock the sequence is declared with, which its operands
  // naming none are evaluated on and which flows no further than the
  // sequence; empty where it is declared with none, `clock` then holding
  // one an instance in it supplied for the monitor. The clock of the
  // declaration a bare instance stands for where its own has none.
  std::vector<EventExpr> declared_clock;
  std::vector<SeqLocalDecl> locals;
  // §16.9.9: the conditions held throughout spans of the flattened chain.
  std::vector<SeqThroughout> throughouts;
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
// Every expression a flattened sequence holds -- its operands, match items,
// throughout conditions -- and those of its intersects, conjuncts and
// alternatives, each handed to `fn` once.
void ForEachLinearSequenceExpr(const LinearSequence& body,
                               const std::function<void(const Expr*)>& fn);

bool FlattenLinearSequence(const ModuleItem* seq, SimContext& ctx, Arena& arena,
                           LinearSequence& out);

// §16.13.1: the clock the operand at `pos` is evaluated on, empty for the
// leading clock, and its number, 0 where the property has not numbered it.
const std::vector<EventExpr>& OperandClock(const LinearSequence& body,
                                           size_t pos);
int OperandClockIndex(const LinearSequence& body, size_t pos);

// §16.13.1: whether an operand of the sequence is evaluated on a clock
// other than the sequence's own, told by the edges and the signals'
// spellings.
bool NamesAnotherClock(const LinearSequence& body);

// §16.8 and §16.12: the actuals of `instance`, an instance of the named
// sequence or property `decl` written as a call, bound to the declaration's
// formals, by position for the leading actuals and by name for the
// `.formal(actual)` ones, each cast as §16.8.1 has it for the formal's
// type; empty for an instance written as a name alone.
// §16.8.1 (b): an instantiated sequence's or property's clock with its
// formals replaced by the actuals: an event actual supplies the edge and
// the signal, an ordinary actual the signal alone under the edge the clock
// wrote.
std::vector<EventExpr> SubstituteClock(const std::vector<EventExpr>& clock,
                                       const ActualsByFormal& actuals,
                                       Arena& arena);

ActualsByFormal BindInstanceActuals(const ModuleItem* decl,
                                    const Expr* instance, Arena& arena);

// §F.4.1: a copy of the flattened `body` with the actuals substituted for
// the formals in its operands, the bounds of its delays, its match items
// and its throughout conditions, and likewise in the operands under its
// intersect, and and or.
LinearSequence SubstituteLinearSequence(const LinearSequence& body,
                                        const ActualsByFormal& actuals,
                                        SimContext& ctx, Arena& arena);

// A literal holding `value`, its width and sign kept, for an expression
// that reads the value as it stood; the copy of a local of a named property
// is one, rewritten in place as the local is assigned (§16.13.7).
Expr* LiteralOfValue(const Logic4Vec& value, Arena& arena);

}  // namespace delta
