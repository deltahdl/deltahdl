#pragma once

#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {

// §F.5.3.3 defines non-vacuity, the relation w |=^non P, between a word w over
// Sigma and a property P. An evaluation of P on w is nonvacuous exactly when
// w |=^non P holds. The relation is given inductively over the property forms
// of the §F.3.2 grammar (assuming, as in §F.5.3, that no local variables are
// involved). It is layered on §F.5.3.1's neutral satisfaction w |= P (a
// satisfied dependency) -- used for the sequence trigger of an implication, the
// "P1 and not P2" guard of an until, and the abort/disable completions -- and
// on the §F.5 word operations (suffix w^{i.}, letterwise complement w-bar,
// finite prefixes, and the T^omega / _|_^omega tails).
//
// §F.5.3.3 also states a rule of its own for ten derived operators of
// §F.3.4.3 -- iff, implies, s_until, always, always [m:n], s_always [m:n],
// s_eventually, eventually [m:n], s_eventually [m:n] and reject_on -- each
// over the operands of the operator rather than over its unfolding, and the
// two need not agree: (p1 implies p2) unfolds to (not p1 or p2), which is
// nonvacuous wherever the complement leaves p1 nonvacuous, where the stated
// rule asks that p1 hold and be nonvacuous and that p2 be nonvacuous; and
// (always p) unfolds to (p until 0), whose until rule is met at the first
// letter by the base case for the Boolean 0, where the stated rule asks for a
// letter from which p is nonvacuous and before which p holds. The property
// model of §F.5.3.1 carries only the primitives, so each stated rule is given
// below as a relation over the operands, named for its operator. For the
// derived operators the subclause states no rule for, it closes, the relation
// is implicitly defined by unrolling their derivation, which
// NonVacuouslyEvaluates on the unfolded form of §F.3.4.3 already is.

// §F.5.3.3: non-vacuity w |=^non P of a property P by a word w. strong(R) and
// weak(R) are nonvacuous on every word; the remaining forms recurse per the
// inductive rules of the subclause.
bool NonVacuouslyEvaluates(const Word& word, const PropertyExpr& property);

// §F.5.3.3: non-vacuity of an (unclocked) top-level property. A bare property
// defers to NonVacuouslyEvaluates; disable iff (b) P applies the subclause's
// disable iff rule; a parenthesized top-level property is transparent.
bool NonVacuouslyEvaluatesTopLevel(const Word& word,
                                   const TopLevelProperty& top);

// §F.5.3.3: w |=^non ( P1 iff P2 ) iff w |=^non P1 or w |=^non P2.
bool NonVacuouslyEvaluatesIff(const Word& word, const PropertyExpr& p1,
                              const PropertyExpr& p2);

// §F.5.3.3: w |=^non ( P1 implies P2 ) iff w |= P1, w |=^non P1 and
// w |=^non P2.
bool NonVacuouslyEvaluatesImplies(const Word& word, const PropertyExpr& p1,
                                  const PropertyExpr& p2);

// §F.5.3.3: w |=^non ( P1 s_until P2 ) by the rule of ( P1 until P2 ): some
// 0 <= i < |w| has w^{i.} |=^non P1 or w^{i.} |=^non P2, and
// w^{j.} |= ( P1 and not P2 ) for all 0 <= j < i.
bool NonVacuouslyEvaluatesSUntil(const Word& word, const PropertyExpr& p1,
                                 const PropertyExpr& p2);

// §F.5.3.3: w |=^non ( always P ) iff some 0 <= i < |w| has w^{i.} |=^non P
// and w^{j.} |= P for all 0 <= j < i.
bool NonVacuouslyEvaluatesAlways(const Word& word, const PropertyExpr& p);

// §F.5.3.3: w |=^non ( always [m:n] P ) and w |=^non ( s_always [m:n] P ) iff
// some m <= i <= n has w^{i.} |=^non P and w^{j.} |= P for all m <= j < i;
// the index is bounded by n alone, w^{i.} being the empty word past |w|.
bool NonVacuouslyEvaluatesAlwaysRange(const Word& word, const PropertyExpr& p,
                                      unsigned int m, unsigned int n);
bool NonVacuouslyEvaluatesSAlwaysRange(const Word& word, const PropertyExpr& p,
                                       unsigned int m, unsigned int n);

// §F.5.3.3: w |=^non ( s_eventually P ) iff some 0 <= i < |w| has
// w^{i.} |=^non P and w^{j.} |= not P for all 0 <= j < i.
bool NonVacuouslyEvaluatesSEventually(const Word& word, const PropertyExpr& p);

// §F.5.3.3: w |=^non ( eventually [m:n] P ) and
// w |=^non ( s_eventually [m:n] P ) iff some m <= i <= n has
// w^{i.} |=^non P and w^{j.} |= not P for all m <= j < i.
bool NonVacuouslyEvaluatesEventuallyRange(const Word& word,
                                          const PropertyExpr& p, unsigned int m,
                                          unsigned int n);
bool NonVacuouslyEvaluatesSEventuallyRange(const Word& word,
                                           const PropertyExpr& p,
                                           unsigned int m, unsigned int n);

// §F.5.3.3: w |=^non ( reject_on (b) P ) by the shape of accept_on and
// disable iff: w |=^non P and either no letter of w satisfies b or some
// prefix x of w free of b has x _|_^omega |= P or x T^omega |/= P.
bool NonVacuouslyEvaluatesRejectOn(const Word& word, const BooleanExpr& b,
                                   const PropertyExpr& p);

// §F.5.3.3: "A word w satisfies property P nonvacuously iff w |= P and
// w |=^non P." Combines §F.5.3.1's neutral satisfaction with non-vacuity.
bool SatisfiesNonVacuously(const Word& word, const PropertyExpr& property);

// §F.5.3.3: the same nonvacuous-satisfaction test for a top-level property,
// pairing §F.5.3.1's NeutrallySatisfiesTopLevel with non-vacuity.
bool SatisfiesTopLevelNonVacuously(const Word& word,
                                   const TopLevelProperty& top);

}  // namespace delta
