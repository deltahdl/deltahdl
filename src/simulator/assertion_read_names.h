#pragma once

#include <string>
#include <unordered_set>

#include "common/arena.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

class SimContext;

void CollectSampledOperandNames(const Expr* e,
                                std::unordered_set<std::string>& out);

void CollectSequenceReadNames(const ModuleItem* seq, SimContext& ctx,
                              Arena& arena,
                              std::unordered_set<std::string>& names);

void CollectPropertyTreeReadNames(const PropertyExprNode* node, SimContext& ctx,
                                  Arena& arena,
                                  std::unordered_set<std::string>& names);

}  // namespace delta
