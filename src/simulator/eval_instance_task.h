#pragma once

#include "common/types.h"
#include "simulator/eval_function_internal.h"

namespace delta {

class Arena;
class SimContext;
struct Expr;

bool SetupInstanceTaskCall(const Expr* expr, SimContext& ctx, Arena& arena,
                           InstanceMethodInfo& call);
void TeardownInstanceTaskCall(const InstanceMethodInfo& call, const Expr* expr,
                              SimContext& ctx, Arena& arena);

void ExecCallStmtExpr(const Expr* expr, SimContext& ctx, Arena& arena);

bool TryEvalParenFreeMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out);

}  // namespace delta
