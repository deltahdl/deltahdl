#pragma once

#include <map>
#include <set>
#include <string>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {

using LocalContext = std::map<std::string, Letter>;

std::set<std::string> ContextDomain(const LocalContext& context);

LocalContext RestrictContext(const LocalContext& context,
                             const std::set<std::string>& domain);

LocalContext RemoveName(const LocalContext& context, const std::string& name);

LocalContext RestrictToName(const LocalContext& context,
                            const std::string& name);

bool LetterEqual(const Letter& lhs, const Letter& rhs);

bool LocalContextEqual(const LocalContext& lhs, const LocalContext& rhs);

std::vector<LocalContext> TightSatisfactionOutputs(const Word& word,
                                                   const SequenceExpr& sequence,
                                                   const LocalContext& input);

bool TightlySatisfiesWithLocals(const Word& word, const SequenceExpr& sequence,
                                const LocalContext& input,
                                const LocalContext& output);

bool IsNondegenerateSequenceWithLocals(const SequenceExpr& sequence);

}  // namespace delta
