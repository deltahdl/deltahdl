#pragma once

#include "common/types.h"
#include "simulator/eval_function_internal.h"

namespace delta {

struct Expr;
struct Stmt;
class SimContext;
class Arena;

bool TryAssocElementNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

bool TryEvalAssocElementMember(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out);

bool ResolveAssocElementMethod(const Expr* access, SimContext& ctx,
                               Arena& arena, InstanceMethodInfo& info,
                               bool report_null);

bool TryEvalAssocElementMethodCall(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out);

}  // namespace delta
