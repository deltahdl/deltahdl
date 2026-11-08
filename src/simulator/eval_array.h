#pragma once

#include <cstdint>
#include <string_view>
#include <vector>

#include "common/types.h"

namespace delta {

struct Expr;
struct ArrayInfo;
struct AssocArrayObject;
struct QueueObject;
class SimContext;
class Arena;

void NotifyOwningVar(SimContext& ctx, std::string_view var_name);

bool TryEvalArrayMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                            Logic4Vec& out);

bool TryEvalArrayReductionWithClause(const Expr* expr, SimContext& ctx,
                                     Arena& arena, Logic4Vec& out);

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

std::vector<Logic4Vec> AssocIndexValues(const AssocArrayObject* aa,
                                        Arena& arena);

bool TryCollectLocatorResult(const Expr* expr, SimContext& ctx, Arena& arena,
                             std::vector<Logic4Vec>& out);

struct LocatorRows {
  std::string_view array_name;
  const ArrayInfo* info = nullptr;
  const QueueObject* queue = nullptr;
  std::vector<uint32_t> offsets;
};

bool TryCollectLocatorRows(const Expr* expr, SimContext& ctx, Arena& arena,
                           LocatorRows& out);

bool TryCollectAssocMapResult(const Expr* expr, SimContext& ctx, Arena& arena,
                              AssocArrayObject& out);

bool CollectQueueOrAssocValues(std::string_view name, SimContext& ctx,
                               std::vector<Logic4Vec>& out);

}  // namespace delta
