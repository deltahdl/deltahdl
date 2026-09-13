#pragma once

#include "elaborator/annex_f_finite_word_satisfaction.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction_local_variables_clocked.h"
#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {

// §F.5.6.2 defines weak and strong satisfaction of an assertion statement by
// a finite word with local variables by one sentence: the definition is that
// of §F.5.3.2, with the understanding that the underlying properties can have
// local variables. So w |=^- A iff w T^omega |= A and w |=^+ A iff
// w _|_^omega |= A as before, the relation on the completion now the neutral
// satisfaction of §F.5.6.1 (NeutrallySatisfiesAssertionWithLocalsWithTail, a
// satisfied dependency) over a statement whose body may declare and sample
// local variables, and the four verdicts of §F.5.3.2 and their conditions
// follow unchanged, the neutral verdict being §F.5.6.1's on the word itself.

// §F.5.6.2: w |=^- A, the finite word completed with T^omega.
bool WeaklySatisfiesByFiniteWordWithLocals(
    const Word& word, const BooleanExpr& enabling,
    const LvAssertionStatement& assertion);

// §F.5.6.2: w |=^+ A, the finite word completed with _|_^omega.
bool StronglySatisfiesByFiniteWordWithLocals(
    const Word& word, const BooleanExpr& enabling,
    const LvAssertionStatement& assertion);

// §F.5.6.2: the verdict of §F.5.3.2 a tool should return for the finite word
// w against A, and the condition the subclause states for each, in its own
// terms, as FiniteWordVerdictCondition has them for §F.5.3.2.
FiniteWordVerdict CheckFiniteWordWithLocals(
    const Word& word, const BooleanExpr& enabling,
    const LvAssertionStatement& assertion);
bool FiniteWordVerdictConditionWithLocals(
    FiniteWordVerdict verdict, const Word& word, const BooleanExpr& enabling,
    const LvAssertionStatement& assertion);

}  // namespace delta
