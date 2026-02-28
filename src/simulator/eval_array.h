#pragma once

#include <vector>

#include "common/types.h"

namespace delta {

struct Expr;
class SimContext;
class Arena;

// §7.12: Array method dispatch (eval_array.cpp).
bool TryEvalArrayMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                            Logic4Vec& out);

// §7.12: Array method statement dispatch (mutating methods like sort/reverse).
bool TryExecArrayMethodStmt(const Expr* expr, SimContext& ctx, Arena& arena);

// §7.12: Array property access without parens (e.g., arr.sum, arr.size).
bool TryEvalArrayProperty(std::string_view var_name, std::string_view prop,
                          SimContext& ctx, Arena& arena, Logic4Vec& out);

// §7.12: Mutating array property access (e.g., arr.sort, arr.reverse).
bool TryExecArrayPropertyStmt(std::string_view var_name, std::string_view prop,
                              SimContext& ctx, Arena& arena);

// §7.10: Queue method dispatch.
bool TryEvalQueueMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                            Logic4Vec& out);
bool TryExecQueueMethodStmt(const Expr* expr, SimContext& ctx, Arena& arena);
bool TryEvalQueueProperty(std::string_view var_name, std::string_view prop,
                          SimContext& ctx, Arena& arena, Logic4Vec& out);
bool TryExecQueuePropertyStmt(std::string_view var_name, std::string_view prop,
                              SimContext& ctx, Arena& arena);

// §7.8: Associative array method dispatch.
bool TryEvalAssocMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                            Logic4Vec& out);
bool TryExecAssocMethodStmt(const Expr* expr, SimContext& ctx, Arena& arena);
bool TryEvalAssocProperty(std::string_view var_name, std::string_view prop,
                          SimContext& ctx, Arena& arena, Logic4Vec& out);
bool TryExecAssocPropertyStmt(std::string_view var_name, std::string_view prop,
                              SimContext& ctx, Arena& arena);

// §7.12.1: Locator method dispatch — returns elements/indices into a vector.
bool TryCollectLocatorResult(const Expr* expr, SimContext& ctx, Arena& arena,
                             std::vector<Logic4Vec>& out);

}  // namespace delta
