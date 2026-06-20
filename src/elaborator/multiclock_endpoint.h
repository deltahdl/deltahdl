#pragma once

#include <string_view>

#include "elaborator/sequence_method.h"

namespace delta {

// §16.13.5 covers detecting and using the end point of a sequence in a
// multiclock context. It builds on the `triggered` and `matched` methods
// defined in §16.13.6 (see "elaborator/sequence_method.h"); the operand-kind,
// single-bit-result, and start-point-independence rules are shared from there.

// §16.13.5: method `triggered` can detect the end point of a multiclocked
// sequence, or detect a sequence's end point from within a multiclocked
// sequence. In both cases the ending clock of the sequence instance to which
// `triggered` is applied shall be the same as the clock in the context where
// the application of `triggered` appears. (The same rule is stated in
// §16.9.11.) Returns true when the requirement is met.
bool TriggeredEndingClockMatchesContext(std::string_view ending_clock,
                                        std::string_view context_clock);

// §16.13.5: to detect the end point of a sequence when the clock of the source
// sequence differs from that of the destination sequence, method `matched` on
// the source sequence is used. The end point of a sequence is reached whenever
// there is a match on its expression. Returns true when `matched` is the
// applicable method for the given source/destination clocks (i.e., they
// differ).
bool MatchedDetectsCrossClockEndPoint(std::string_view source_clock,
                                      std::string_view destination_clock);

// §16.13.5: like `triggered`, `matched` can be applied to sequences that have
// formal arguments.
bool MatchedAllowedOnSequenceWithFormalArguments();

// §16.13.5: local variables can be passed into an instance of a named sequence
// to which `matched` is applied. The same restrictions apply as for
// `triggered`, and values of local variables sampled in such an instance flow
// out under the same conditions as for `triggered` (see §16.10).
bool MatchedLocalVariableRulesSameAsTriggered();

// §16.13.5: a sequence instance to which `matched` is applied can have multiple
// matches within a single cycle of the destination sequence clock. The multiple
// matches are treated semantically the same way as matching both disjuncts of
// an `or`; the evaluating thread forks to account for the distinct
// local-variable valuations.
bool MatchedMultipleMatchesTreatedAsOrDisjuncts();

// §16.13.5: unlike `triggered`, `matched` stores the result of the source
// sequence match until the arrival of the first destination clock tick after
// the match, synchronizing between the two clocks. Reuses the persistence model
// from §16.13.6.
bool MatchedSynchronizesAcrossClocks();

}  // namespace delta
