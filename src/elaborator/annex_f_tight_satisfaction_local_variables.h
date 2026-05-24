#pragma once

#include <map>
#include <set>
#include <string>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {

// §F.5.5 extends the tight-satisfaction relation of §F.5.2 to sequences that
// carry local variables. A local variable context is a function assigning a
// value to each local variable name; here a value is modelled as the alphabet
// letter observed where the assignment happens, which is the realization of
// e[L_0, w^0] for the elementary case the §F.3.2 grammar can express (the
// sampling form (1, v = e) records only the name v). When the observed letter
// is T or _|_, §F.5.5 permits any constant of e's type; the observed letter is
// stored as the canonical representative of that freedom.
using LocalContext = std::map<std::string, Letter>;

// §F.5.5: dom(L), the set of local variable names in the domain of a context.
std::set<std::string> ContextDomain(const LocalContext& context);

// §F.5.5: L|_D, the context restricted to the domain D (a subset of dom(L)).
LocalContext RestrictContext(const LocalContext& context,
                             const std::set<std::string>& domain);

// §F.5.5: L\v, the context with the name v removed from its domain.
LocalContext RemoveName(const LocalContext& context, const std::string& name);

// §F.5.5: L[v], the context restricted to the single name v (empty if v is not
// in the domain).
LocalContext RestrictToName(const LocalContext& context,
                            const std::string& name);

// §F.5: two letters are equal when they denote the same alphabet element.
bool LetterEqual(const Letter& lhs, const Letter& rhs);

// §F.5.5: two local variable contexts are equal when they bind the same names
// to equal values.
bool LocalContextEqual(const LocalContext& lhs, const LocalContext& rhs);

// §F.5.5: every output context L_1 such that w, L_0, L_1 |== R, given the word
// w and the input context L_0. The relation is nondeterministic, so a set of
// contexts is returned; it is empty exactly when no L_1 satisfies the relation.
// A clocked sequence is first reduced to its §F.5.1.1 unclocked rewrite.
std::vector<LocalContext> TightSatisfactionOutputs(const Word& word,
                                                   const SequenceExpr& sequence,
                                                   const LocalContext& input);

// §F.5.5: the four-way relation w, L_0, L_1 |== R as a predicate, true when the
// given output context is among the contexts the relation yields.
bool TightlySatisfiesWithLocals(const Word& word, const SequenceExpr& sequence,
                                const LocalContext& input,
                                const LocalContext& output);

// §F.5.5: an unclocked sequence is nondegenerate iff some nonempty finite word
// and contexts L_0, L_1 tightly satisfy it; a clocked sequence is so iff its
// unclocked rewrite is. The witness search is bounded, which is exact for the
// finite sequences this model is exercised on.
bool IsNondegenerateSequenceWithLocals(const SequenceExpr& sequence);

}  // namespace delta
