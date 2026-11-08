#pragma once

#include "elaborator/annex_f_finite_word_satisfaction.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction_local_variables_clocked.h"
#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {

bool WeaklySatisfiesByFiniteWordWithLocals(
    const Word& word, const BooleanExpr& enabling,
    const LvAssertionStatement& assertion);

bool StronglySatisfiesByFiniteWordWithLocals(
    const Word& word, const BooleanExpr& enabling,
    const LvAssertionStatement& assertion);

FiniteWordVerdict CheckFiniteWordWithLocals(
    const Word& word, const BooleanExpr& enabling,
    const LvAssertionStatement& assertion);
bool FiniteWordVerdictConditionWithLocals(
    FiniteWordVerdict verdict, const Word& word, const BooleanExpr& enabling,
    const LvAssertionStatement& assertion);

}  // namespace delta
