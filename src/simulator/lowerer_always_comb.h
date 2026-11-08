#pragma once

#include <string_view>
#include <vector>

#include "parser/ast_stmt.h"

namespace delta {

class Arena;
class SimContext;

std::vector<std::string_view> UnpackedElementNames(std::string_view name,
                                                   SimContext& ctx);

const std::vector<EventExpr>& ImplicitListEvents(
    const std::vector<EventExpr>& sens, SimContext& ctx, Arena& arena);

std::vector<std::string_view> AlwaysCombWatchedNames(
    const Stmt* body, const std::vector<EventExpr>& sens, SimContext& ctx);

}  // namespace delta
