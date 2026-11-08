#pragma once

#include <cstdint>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_name_tables.h"

namespace delta {

bool PassedAsWholeActual(const Expr* instance, std::string_view name);

std::vector<DeclaredNameTables::MatchLocals> NamedMatchLocals(
    const std::vector<SeqLocalDecl>& locals,
    const std::vector<std::vector<Logic4Vec>>& ended);

const std::vector<DeclaredNameTables::MatchLocals>* FlowedMatches(
    const Expr* operand, SimContext& ctx);

void TakeFlowedLocals(const Expr* operand, uint32_t pick, SimContext& ctx,
                      Arena& arena);

}  // namespace delta
