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
  std::vector<EventExpr> clock;
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
// to the clockless sequences it instantiates. Answers false where `seq` has
// no linear body the parser captured, where an instance names a sequence that
// has none, or where instances nest past the depth a cyclic dependency, which
// §16.8 makes an error, would reach.
bool FlattenLinearSequence(const ModuleItem* seq, SimContext& ctx, Arena& arena,
                           LinearSequence& out);

}  // namespace delta
