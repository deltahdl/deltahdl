#pragma once

#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {

// §F.5.3.3 defines non-vacuity, the relation w |=^non P, between a word w over
// Sigma and a property P. An evaluation of P on w is nonvacuous exactly when
// w |=^non P holds. The relation is given inductively over the property forms of
// the §F.3.2 grammar (assuming, as in §F.5.3, that no local variables are
// involved). It is layered on §F.5.3.1's neutral satisfaction w |= P (a
// satisfied dependency) -- used for the sequence trigger of an implication, the
// "P1 and not P2" guard of an until, and the abort/disable completions -- and on
// the §F.5 word operations (suffix w^{i.}, letterwise complement w-bar, finite
// prefixes, and the T^omega / _|_^omega tails).
//
// §F.5.3.3 also lists |=^non rules for the derived property operators (iff,
// implies, s_until, always, always[m:n], s_always[m:n], s_eventually,
// eventually[m:n], s_eventually[m:n], reject_on). The standard states that for
// the derived operators the relation is "implicitly defined by unrolling their
// derivation", and those operators are not part of the §F.3.2/§F.5.3.1 abstract
// syntax this model evaluates (PropertyExpr carries only the primitives). So
// this file covers exactly the primitive forms the property model represents,
// which is precisely the set §F.5.3.3 gives an explicit |=^non rule for among
// them: the two base cases strong(R)/weak(R) and the inductive cases for ( P ),
// R |-> P, and/or, not, nexttime, until, and accept_on. The top-level disable
// iff (b) P rule is provided over §F.5.3.1's TopLevelProperty, where disable iff
// is modeled.

// §F.5.3.3: non-vacuity w |=^non P of a property P by a word w. strong(R) and
// weak(R) are nonvacuous on every word; the remaining forms recurse per the
// inductive rules of the subclause.
bool NonVacuouslyEvaluates(const Word& word, const PropertyExpr& property);

// §F.5.3.3: non-vacuity of an (unclocked) top-level property. A bare property
// defers to NonVacuouslyEvaluates; disable iff (b) P applies the subclause's
// disable iff rule; a parenthesized top-level property is transparent.
bool NonVacuouslyEvaluatesTopLevel(const Word& word,
                                   const TopLevelProperty& top);

// §F.5.3.3: "A word w satisfies property P nonvacuously iff w |= P and
// w |=^non P." Combines §F.5.3.1's neutral satisfaction with non-vacuity.
bool SatisfiesNonVacuously(const Word& word, const PropertyExpr& property);

// §F.5.3.3: the same nonvacuous-satisfaction test for a top-level property,
// pairing §F.5.3.1's NeutrallySatisfiesTopLevel with non-vacuity.
bool SatisfiesTopLevelNonVacuously(const Word& word,
                                   const TopLevelProperty& top);

}  // namespace delta
