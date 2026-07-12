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

// Applies a §7.12.3 reduction whose with clause is attached to a bare
// member-access node (arr.sum with (e), the parenthesis-free LRM form). Returns
// false for anything that is not such a reduction so the caller continues with
// ordinary member resolution.
bool TryEvalArrayReductionWithClause(const Expr* expr, SimContext& ctx,
                                     Arena& arena, Logic4Vec& out);

// Applies a §7.12.2 sort()/rsort() with-clause ordering key when the ordering
// call reaches evaluation as a bare member-access node: the parenthesis-free
// form (a.sort with (e), the LRM's own syntax) and every queue receiver, which
// the call-form executor does not cover. Reorders the array or queue in place
// and returns true; returns false for anything that is not such an ordering
// call so the caller falls back to ordinary member resolution.
bool TryExecArrayOrderingWithClauseStmt(const Expr* expr, SimContext& ctx,
                                        Arena& arena);

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
