#pragma once

#include <memory>

#include "elaborator/annex_f_grammar.h"

namespace delta {

// §F.5.1.1 defines the transformation T^s(S, c): given a sequence and a clock
// c, it produces an equivalent unclocked sequence by pushing the clock down to
// every Boolean. The rewrite consumes and produces the §F.3.2 sequence model,
// so the result can be fed straight into the unclocked tight-satisfaction
// relation of §F.5.2.
//
// `clock` is the Boolean expression c that names the current clock. The base
// rule rewrites a Boolean b into (!c[*0:$] ##1 c & b), and a nested clock form
// @(c2) r discards the incoming clock in favor of c2.
std::shared_ptr<const SequenceExpr> RewriteSequenceUnderClock(
    const SequenceExpr& sequence,
    const std::shared_ptr<const BooleanExpr>& clock);

// §F.5.2 refers to "the unclocked sequence that results from S by applying the
// rewrite rules". A clocked sequence carries its own leading clock in its
// @( b ) form, so this helper extracts that clock and applies §F.5.1.1.
std::shared_ptr<const SequenceExpr> RewriteClockedSequence(
    const SequenceExpr& sequence);

// §F.5.1 places a precondition on the clock rewrite: "it is required that the
// conditions in event controls not be dependent upon any local variables." The
// rewrite of §F.5.1.1 pushes each @( c ) event condition c down onto the
// Booleans of the sequence, so the reduction is only well defined when no such
// condition reads a local variable of the sequence. This returns true iff every
// clock event in `sequence` is independent of the local variable names the
// sequence declares or samples, and false as soon as one event condition names
// such a variable.
bool ClockEventsAreLocalVariableIndependent(const SequenceExpr& sequence);

}  // namespace delta
