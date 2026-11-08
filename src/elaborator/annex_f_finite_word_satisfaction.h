#pragma once

#include <cstdint>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {

bool WeaklySatisfiesByFiniteWord(const Word& word, const BooleanExpr& enabling,
                                 const AssertionStatement& assertion);

bool StronglySatisfiesByFiniteWord(const Word& word,
                                   const BooleanExpr& enabling,
                                   const AssertionStatement& assertion);

enum class FiniteWordVerdict : std::uint8_t {
  kHoldsStrongly,
  kFails,
  kHolds,
  kPending,
};

FiniteWordVerdict CheckFiniteWord(const Word& word, const BooleanExpr& enabling,
                                  const AssertionStatement& assertion);

bool FiniteWordVerdictCondition(FiniteWordVerdict verdict, const Word& word,
                                const BooleanExpr& enabling,
                                const AssertionStatement& assertion);

const char* FiniteWordVerdictLabel(FiniteWordVerdict verdict);

}  // namespace delta
