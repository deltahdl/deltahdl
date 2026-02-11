#pragma once

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

}  // namespace delta
