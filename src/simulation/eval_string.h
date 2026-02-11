#pragma once

#include "common/types.h"

namespace delta {

struct Expr;
class SimContext;
class Arena;

// §6.16: String method dispatch (eval_string.cpp).
bool TryEvalStringMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                             Logic4Vec& out);

}  // namespace delta
