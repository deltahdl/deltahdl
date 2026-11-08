#pragma once

#include <cstddef>
#include <memory>
#include <set>
#include <string>
#include <vector>

#include "elaborator/annex_f_extended_expressions.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"

namespace delta {

struct ExtendedBooleanQuery {
  const Word& word;
  std::size_t j;
  const SequenceExpr& sequence;
  const std::set<std::string>& actuals;
};

std::vector<LocalContext> TriggeredOutputs(const ExtendedBooleanQuery& query,
                                           const LocalContext& input);

bool TriggeredSatisfies(const ExtendedBooleanQuery& query,
                        const LocalContext& input, const LocalContext& output);

std::vector<LocalContext> MatchedOutputs(
    const ExtendedBooleanQuery& query,
    const std::shared_ptr<const BooleanExpr>& clock, const LocalContext& input);

bool MatchedSatisfies(const ExtendedBooleanQuery& query,
                      const std::shared_ptr<const BooleanExpr>& clock,
                      const LocalContext& input, const LocalContext& output);

ExtendedExpression TriggeredExpression(
    std::shared_ptr<const SequenceExpr> sequence,
    std::set<std::string> actuals);
ExtendedExpression MatchedExpression(
    std::shared_ptr<const SequenceExpr> sequence, std::set<std::string> actuals,
    std::shared_ptr<const BooleanExpr> clock);

}  // namespace delta
