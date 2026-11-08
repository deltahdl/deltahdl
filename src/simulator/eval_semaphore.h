#pragma once

#include <cstdint>
#include <string_view>

#include "common/types.h"

namespace delta {

struct Expr;
struct SemaphoreObject;
struct Stmt;
class Arena;
class SimContext;

SemaphoreObject* SemaphoreCallTarget(const Expr* expr, SimContext& ctx,
                                     std::string_view method);

bool ReportNegativeKeyCount(const Expr* expr, int32_t count,
                            std::string_view subclause, SimContext& ctx);

int32_t SemaphoreKeyArg(const Expr* expr, SimContext& ctx, Arena& arena,
                        int32_t absent);

bool TryEvalSemaphoreMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out);

bool TryExecSemaphoreCallInFunction(const Expr* expr, SimContext& ctx,
                                    Arena& arena);

std::string_view ScopedOrBareTargetKey(const Expr* lhs, Arena& arena);

bool TrySemaphoreNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

}  // namespace delta
