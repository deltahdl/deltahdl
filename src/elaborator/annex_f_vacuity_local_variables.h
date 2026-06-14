#pragma once

#include "elaborator/annex_f_neutral_satisfaction_local_variables.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"

namespace delta {

// §F.5.6.3 defines vacuity in the presence of local variables. Its one-sentence
// body is the governing rule: the definition is identical to that without local
// variables (§F.5.3.3, a satisfied dependency), but with the understanding that
// the underlying properties can have local variables, and with the added rule
//
//   w, L_0 |=^non ( t v ; P ) iff w, L_0\v |=^non P.
//
// So the non-vacuity relation |=^non is carried over §F.5.6.1's local-variable
// property model (LvProperty / LvTopLevelProperty) rather than §F.5.3.1's
// no-local-variable PropertyExpr, threading an input local variable context L_0
// (§F.5.5's LocalContext) alongside the word. The per-operator rules are exactly
// those of §F.5.3.3:
//
//   * strong(R) and weak(R) are nonvacuous on every word (the context plays no
//     role, as in §F.5.3.3);
//   * ( P ), not P, ( P1 or P2 ), ( P1 and P2 ), ( nexttime P ), and
//     ( P1 until P2 ) recurse per §F.5.3.3 with the context threaded inertly --
//     a conjunction is nonvacuous when either conjunct is, and the until guard
//     "P1 and not P2" is decided by §F.5.6.1's neutral satisfaction with locals;
//   * ( R |-> P ) is nonvacuous when some prefix tightly satisfies the trigger R
//     -- measured on w itself, not w-bar, as in §F.5.3.3 -- under §F.5.5's
//     four-way relation, and the consequent is nonvacuous under an output
//     context L_1 the antecedent yields;
//   * accept_on (b) P and the top-level disable iff (b) P share §F.5.3.3's
//     abort/disable shape, whose prefix completions are decided by §F.5.6.1's
//     neutral satisfaction with locals;
//   * the new local variable declaration form ( t v ; P ) strips the declared
//     name from the context the body sees, the only rule §F.5.6.3 states
//     explicitly.

// §F.5.6.3: non-vacuity w, L_0 |=^non P of a property under an input local
// variable context.
bool NonVacuouslyEvaluatesWithLocals(const Word& word, const LvProperty& property,
                                     const LocalContext& context);

// §F.5.6.3: non-vacuity from no live local variables, starting the recursion
// from the empty context, mirroring §F.5.6.1's "w |= Q iff w, {} |= Q" entry.
bool NonVacuouslyEvaluatesWithLocals(const Word& word,
                                     const LvProperty& property);

// §F.5.6.3: non-vacuity w, L_0 |=^non T of an (unclocked) top-level property. A
// bare property defers to the property rule; disable iff (b) P applies the
// abort/disable shape; a parenthesis is transparent; ( t v ; T ) strips the
// declared name from the context.
bool NonVacuouslyEvaluatesTopLevelWithLocals(const Word& word,
                                             const LvTopLevelProperty& top,
                                             const LocalContext& context);

// §F.5.6.3 inherits §F.5.3.3's "w satisfies P nonvacuously iff w |= P and
// w |=^non P," realized with local variables: §F.5.6.1's neutral satisfaction
// with locals together with this subclause's non-vacuity.
bool SatisfiesNonVacuouslyWithLocals(const Word& word, const LvProperty& property,
                                     const LocalContext& context);

// §F.5.6.3: the same nonvacuous-satisfaction test for a top-level property.
bool SatisfiesTopLevelNonVacuouslyWithLocals(const Word& word,
                                             const LvTopLevelProperty& top,
                                             const LocalContext& context);

}  // namespace delta
