#pragma once

#include <vector>

#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

class PropertyRegistry;

std::vector<EventExpr> SemanticLeadingClocks(
    const PropertyExprNode* node, const std::vector<EventExpr>& outer,
    const PropertyRegistry& registry);

std::vector<EventExpr> DeterminedLeadingClock(const PropertyExprNode* node,
                                              const PropertyRegistry& registry);

std::vector<EventExpr> DeterminedSequenceClock(
    const ModuleItem* seq, const PropertyRegistry& registry);

bool HasUniqueSemanticLeadingClock(const PropertyExprNode* node,
                                   const std::vector<EventExpr>& outer,
                                   const PropertyRegistry& registry);

bool TreeNamesOnlyClock(const PropertyExprNode* node,
                        const std::vector<EventExpr>& clock,
                        const PropertyRegistry& registry);

}  // namespace delta
