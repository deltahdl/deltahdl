#pragma once

#include <vector>

#include "common/types.h"

namespace delta {

struct Expr;
struct AssocArrayObject;
class SimContext;
class Arena;

bool TryEvalArrayMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                            Logic4Vec& out);

bool TryExecArrayMethodStmt(const Expr* expr, SimContext& ctx, Arena& arena);

bool TryEvalArrayProperty(std::string_view var_name, std::string_view prop,
                          SimContext& ctx, Arena& arena, Logic4Vec& out);

bool TryExecArrayPropertyStmt(std::string_view var_name, std::string_view prop,
                              SimContext& ctx, Arena& arena);

bool TryEvalQueueMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                            Logic4Vec& out);
bool TryExecQueueMethodStmt(const Expr* expr, SimContext& ctx, Arena& arena);
bool TryEvalQueueProperty(std::string_view var_name, std::string_view prop,
                          SimContext& ctx, Arena& arena, Logic4Vec& out);
bool TryExecQueuePropertyStmt(std::string_view var_name, std::string_view prop,
                              SimContext& ctx, Arena& arena);

bool TryEvalAssocMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                            Logic4Vec& out);
bool TryExecAssocMethodStmt(const Expr* expr, SimContext& ctx, Arena& arena);
bool TryEvalAssocProperty(std::string_view var_name, std::string_view prop,
                          SimContext& ctx, Arena& arena, Logic4Vec& out);
bool TryExecAssocPropertyStmt(std::string_view var_name, std::string_view prop,
                              SimContext& ctx, Arena& arena);

bool TryCollectLocatorResult(const Expr* expr, SimContext& ctx, Arena& arena,
                             std::vector<Logic4Vec>& out);

bool TryCollectAssocMapResult(const Expr* expr, SimContext& ctx, Arena& arena,
                              AssocArrayObject& out);

}  // namespace delta
