#pragma once

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction_local_variables.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"

namespace delta {

bool NonVacuouslyEvaluatesWithLocals(const Word& word,
                                     const LvProperty& property,
                                     const LocalContext& context);

bool NonVacuouslyEvaluatesWithLocals(const Word& word,
                                     const LvProperty& property);

bool NonVacuouslyEvaluatesTopLevelWithLocals(const Word& word,
                                             const LvTopLevelProperty& top,
                                             const LocalContext& context);

bool NonVacuouslyEvaluatesIffWithLocals(const Word& word, const LvProperty& p1,
                                        const LvProperty& p2,
                                        const LocalContext& context);
bool NonVacuouslyEvaluatesImpliesWithLocals(const Word& word,
                                            const LvProperty& p1,
                                            const LvProperty& p2,
                                            const LocalContext& context);
bool NonVacuouslyEvaluatesSUntilWithLocals(const Word& word,
                                           const LvProperty& p1,
                                           const LvProperty& p2,
                                           const LocalContext& context);
bool NonVacuouslyEvaluatesAlwaysWithLocals(const Word& word,
                                           const LvProperty& p,
                                           const LocalContext& context);
bool NonVacuouslyEvaluatesAlwaysRangeWithLocals(const Word& word,
                                                const LvProperty& p,
                                                unsigned int m, unsigned int n,
                                                const LocalContext& context);
bool NonVacuouslyEvaluatesSAlwaysRangeWithLocals(const Word& word,
                                                 const LvProperty& p,
                                                 unsigned int m, unsigned int n,
                                                 const LocalContext& context);
bool NonVacuouslyEvaluatesSEventuallyWithLocals(const Word& word,
                                                const LvProperty& p,
                                                const LocalContext& context);
bool NonVacuouslyEvaluatesEventuallyRangeWithLocals(
    const Word& word, const LvProperty& p, unsigned int m, unsigned int n,
    const LocalContext& context);
bool NonVacuouslyEvaluatesSEventuallyRangeWithLocals(
    const Word& word, const LvProperty& p, unsigned int m, unsigned int n,
    const LocalContext& context);
bool NonVacuouslyEvaluatesRejectOnWithLocals(const Word& word,
                                             const BooleanExpr& b,
                                             const LvProperty& p,
                                             const LocalContext& context);

bool SatisfiesNonVacuouslyWithLocals(const Word& word,
                                     const LvProperty& property,
                                     const LocalContext& context);

bool SatisfiesTopLevelNonVacuouslyWithLocals(const Word& word,
                                             const LvTopLevelProperty& top,
                                             const LocalContext& context);

}  // namespace delta
