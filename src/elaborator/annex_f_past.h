#pragma once

#include <cstddef>
#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <vector>

#include "elaborator/annex_f_extended_expressions.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {

std::vector<std::size_t> PastSourceIndices(
    const Word& word, std::size_t j, unsigned int n,
    const std::shared_ptr<const BooleanExpr>& gate,
    const std::shared_ptr<const BooleanExpr>& clock);

bool PastSamplesInitialValue(const Word& word, std::size_t j, unsigned int n,
                             const std::shared_ptr<const BooleanExpr>& gate,
                             const std::shared_ptr<const BooleanExpr>& clock);

std::optional<std::size_t> PastGclkSourceIndex(const Word& word, std::size_t j);

enum class VariableKind : std::uint8_t { kStatic, kOther };
bool PastInitialValue(VariableKind kind,
                      std::optional<bool> declaration_assignment,
                      bool type_default);

ExtendedExpression PastOfAtom(const std::string& name, unsigned int n,
                              std::shared_ptr<const BooleanExpr> gate,
                              std::shared_ptr<const BooleanExpr> clock,
                              bool initial);

ExtendedExpression PastOfAtom(const std::string& name, bool initial);

}  // namespace delta
