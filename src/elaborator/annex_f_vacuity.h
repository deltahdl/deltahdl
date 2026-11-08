#pragma once

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {

bool NonVacuouslyEvaluates(const Word& word, const PropertyExpr& property);

bool NonVacuouslyEvaluatesTopLevel(const Word& word,
                                   const TopLevelProperty& top);

bool NonVacuouslyEvaluatesIff(const Word& word, const PropertyExpr& p1,
                              const PropertyExpr& p2);

bool NonVacuouslyEvaluatesImplies(const Word& word, const PropertyExpr& p1,
                                  const PropertyExpr& p2);

bool NonVacuouslyEvaluatesSUntil(const Word& word, const PropertyExpr& p1,
                                 const PropertyExpr& p2);

bool NonVacuouslyEvaluatesAlways(const Word& word, const PropertyExpr& p);

bool NonVacuouslyEvaluatesAlwaysRange(const Word& word, const PropertyExpr& p,
                                      unsigned int m, unsigned int n);
bool NonVacuouslyEvaluatesSAlwaysRange(const Word& word, const PropertyExpr& p,
                                       unsigned int m, unsigned int n);

bool NonVacuouslyEvaluatesSEventually(const Word& word, const PropertyExpr& p);

bool NonVacuouslyEvaluatesEventuallyRange(const Word& word,
                                          const PropertyExpr& p, unsigned int m,
                                          unsigned int n);
bool NonVacuouslyEvaluatesSEventuallyRange(const Word& word,
                                           const PropertyExpr& p,
                                           unsigned int m, unsigned int n);

bool NonVacuouslyEvaluatesRejectOn(const Word& word, const BooleanExpr& b,
                                   const PropertyExpr& p);

bool SatisfiesNonVacuously(const Word& word, const PropertyExpr& property);

bool SatisfiesTopLevelNonVacuously(const Word& word,
                                   const TopLevelProperty& top);

}  // namespace delta
