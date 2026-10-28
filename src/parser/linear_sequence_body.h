#pragma once

#include <cstddef>
#include <vector>

#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

// The edits the trial parse of a sequence body makes to the linear form it
// has read so far, each on operands already appended rather than on tokens.

// A delay of exactly 0 ticks, written with no formal's name.
bool IsNoDelay(const SeqCycleDelay& delay);

// §16.7: a delay owed before a group and the delay the group's chain opens
// with add, unbounded where either is. A delay of 0 adds nothing, so the
// other stands as written, a bound named by a formal among it (§16.8), and
// `##n b` keeps n for the instantiation to supply.
SeqCycleDelay AddSeqDelays(const SeqCycleDelay& a, const SeqCycleDelay& b);

// §16.13.1: the clock the operand just appended is evaluated on, kept
// parallel to the operands once any chain of the body writes one, the
// operands before the first written carrying none, the leading clock's.
void PushOperandClock(SeqLinearBody& body, const std::vector<EventExpr>& clock);

// §16.9.2: consecutive repetition of a group by an exact count, unrolled as
// the clause has it, `(a ##2 b)[*3]` being `(a ##2 b) ##1 (a ##2 b) ##1 (a ##2
// b)`: the group's operands from `first` on are appended again `count - 1`
// times, the copy's first operand a tick after the last, each copy on the
// clock its original is on. A group writing a clock of its own is not
// unrolled but read into a sequence of its own, so the clock each copy
// carries is the one in force where the group stands (Annex F.3.2).
bool UnrollGroupRepetition(SeqLinearBody& body, size_t first,
                           const SeqRepetition& rep);

// §16.10 and §16.11: marks `items`, the match items of the group of one
// operand from `first` on in `body`, where the group admits an empty match,
// its operand repeated from zero, `(b[*0:1], x = e)`, not `(a ##1 b[*0:1], x
// = e)`; the elaborator reports them, this parse being a trial one.
void MarkEmptyMatchItems(const SeqLinearBody& body, size_t first,
                         std::vector<SeqMatchAssign>& items);

// §16.9.10: `seq1 within seq2` abbreviates `(1[*0:$] ##1 seq1 ##1 1[*0:$])
// intersect seq2`, so the chain seq1 was read into becomes that first
// operand: `lead`, a 1, repeated any number of times before it, a tick
// between, and `trail`, another, after, its own operands' delays,
// throughouts and clocks moved along, the two 1s on the clock in force.
void WrapWithinOperand(SeqLinearBody& body, Expr* lead, Expr* trail);

}  // namespace delta
