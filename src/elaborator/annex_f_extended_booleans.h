#pragma once

#include <cstddef>
#include <memory>
#include <set>
#include <string>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"

namespace delta {

// §F.6.1 defines two "extended Boolean" expressions -- the sequence-instance
// methods .triggered and .matched -- whose value at a point w^j of a word is
// fixed by the §F.5.5 tight-satisfaction-with-local-variables relation applied
// to subwords ending (or starting) at j. Here T(V) denotes an instance of a
// clocked or unclocked sequence T to which the local variables V are passed as
// actual arguments; V is modelled as the set of those names. The relations are
// nondeterministic in the output context, so each is exposed both as the set of
// output contexts L_1 it yields and as a four-way predicate.

// §F.6.1: the output contexts L_1 such that w^j, L_0, L_1 |= T(V).triggered.
// triggered holds at j iff some start point 0 <= i <= j lets the subword w^{i,j}
// tightly satisfy T from the empty context, producing an inner context L; the
// result keeps the names of L_0 that the call does not overwrite -- the domain
// D = dom(L_0) - (dom(L) & V) -- and adds the names of L that flow back through
// the actual arguments, L|_V.
std::vector<LocalContext> TriggeredOutputs(
    const Word& word, std::size_t j, const SequenceExpr& sequence,
    const std::set<std::string>& actuals, const LocalContext& input);

// §F.6.1: the four-way relation w^j, L_0, L_1 |= T(V).triggered as a predicate,
// true when the given output context is among those TriggeredOutputs yields.
bool TriggeredSatisfies(const Word& word, std::size_t j,
                        const SequenceExpr& sequence,
                        const std::set<std::string>& actuals,
                        const LocalContext& input, const LocalContext& output);

// §F.6.1: the output contexts L_1 such that w^j, L_0, L_1 |= @(c)(T(V).matched).
// matched holds at j with destination clock c iff T(V) is triggered at some
// strictly earlier point i (0 <= i < j) with the same output context, and the
// clock c ticks exactly once between i and j -- the subword w^{i+1,j} tightly
// satisfies the goto repetition c[->1] from empty contexts.
std::vector<LocalContext> MatchedOutputs(
    const Word& word, std::size_t j, const SequenceExpr& sequence,
    const std::set<std::string>& actuals,
    const std::shared_ptr<const BooleanExpr>& clock, const LocalContext& input);

// §F.6.1: the four-way relation w^j, L_0, L_1 |= @(c)(T(V).matched) as a
// predicate, true when the given output context is among those MatchedOutputs
// yields.
bool MatchedSatisfies(const Word& word, std::size_t j,
                      const SequenceExpr& sequence,
                      const std::set<std::string>& actuals,
                      const std::shared_ptr<const BooleanExpr>& clock,
                      const LocalContext& input, const LocalContext& output);

}  // namespace delta
